-- Prove2me | Theorems.Thm_MultiPurchaseMNL_eq_6_knapsack
-- name    : MultiPurchaseMNL.eq_6_knapsack
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:57.642642+00:00
-- url     : https://prove2.me/theorems/98338a2a-b803-4a2d-990f-68d77b0f915a
-- title:
--   (6), p.19 — the knapsack subroutine returns $\tilde S\in\mathcal F$ beating every feasible solution of (5), in $O(n^2/\delta)$ operations
-- statement:
--   Let $H$ be a set of heavy products and $L$ its light set, let $W>0$, $\delta\in(0,1]$, and let $c_i$ be real item values (the algorithm uses $c_i=r_i\tilde\pi_i$). The knapsack subroutine of the algorithm rounds weights down to multiples of $u=\delta W/((1+\delta)^2n)$ and, by dynamic programming over rounded totals, maximizes $\sum_{i\in T}c_i$ over $T\subseteq L$ with rounded total in $[\lceil W/((1+\delta)u)\rceil-n,\lfloor W/u\rfloor]$. Then:
--
--   1. if problem (5) is feasible, that is, some $T'\subseteq L$ has $w(T')\in[W/(1+\delta),W]$, the subroutine returns a set $T$;
--   2. a returned $T$ consists of distinct light products, $\tilde S=H\cup T\in\mathcal F$, and
--   $$
--   \sum_{i\in\tilde S}c_i\ \ge\ \sum_{i\in H\cup T'}c_i\quad\text{for every feasible }T'\text{ of (5)},
--   $$
--   which is (6), $\sum_{\tilde S}r_i\tilde\pi_i\ge\mathrm{OPT}_{\text{knapsack}}\ge\sum_{S^*}r_i\tilde\pi_i$;
--   3. it performs at most $K\,n^2/\delta$ operations, for one universal constant $K$.
--
--   Differences from the source:
--
--   - reading: round weights down to multiples of δW/n; the output violates [W/(1+δ), W] by a factor 1 ± δ and lies in F → grid u = δW/((1+δ)²n), accepted rounded totals [⌈W/((1+δ)u)⌉₊ − n, ⌊W/u⌋₊]; reason: the paper does not place the window; with this grid every feasible set of (5) is accepted and every accepted set has w ∈ [W/(1+δ)², (1+δ)W], as (6) requires
--   - generalization: values rᵢπ̃ᵢ → any real values cᵢ; reason: specializes to cᵢ = rᵢπ̃ᵢ
--   - encoding: O(n²/δ) time → ∃ K universal, operation count ≤ K·n²/δ in the unit-cost model, n ≥ 1, δ ≤ 1; reason: the meaning of O(n²/δ); the grid divides by n, and the paper's δ = ϵ/(6m_max) ≤ 1/6
--   - encoding: L as a set → L passed as any list enumerating light I H without repetition; reason: the same set
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), (5)–(6), pp.18–19

import Mathlib
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_ValueFunction
import Definitions.Def_MultiPurchaseMNL_Algorithm

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), (5)–(6), pp.18–19: "By rounding down
product weights to the nearest multiple of `δW/n`, standard dynamic programming ideas […] can be
employed to compute […] a subset of products `S̃ ∈ F` with
`Σ_{i∈S̃} rᵢπ̃ᵢ ≥ OPT_knapsack ≥ Σ_{i∈S∗} rᵢπ̃ᵢ`" (6).

For the program's knapsack subroutine run on the light set `L` of a heavy set `H`, item values `c`
(the program uses `cᵢ = rᵢπ̃ᵢ`), a guess `W > 0` and `δ ∈ (0, 1]`:
1. if some `T' ⊆ L` has `w(T') ∈ [W/(1+δ), W]` (a feasible solution of (5)), the subroutine returns
   some `T`;
2. whatever `T` it returns is a list of distinct light products with `H ∪ T ∈ F`, and
   `Σ_{i∈H∪T} cᵢ ≥ Σ_{i∈H∪T'} cᵢ` for every feasible `T'` of (5);
3. it performs at most `K · n²/δ` unit-cost operations, for one universal constant `K`.

**Formalization Note.** The grid is `δW/((1+δ)²n)`, not `δW/n`, and the accepted window of rounded
totals is `[⌈W/((1+δ)u)⌉₊ − n, ⌊W/u⌋₊]`; the paper does not place the window (reading 4). `L` is
passed as any list enumerating `light I H` without repetition. `n ≥ 1`: the grid divides by `n`.
`K` is quantified before all the data. -/
theorem eq_6_knapsack :
    ∃ K : ℕ, ∀ {n mmax : ℕ} (I : Instance n mmax), 0 < n → (∀ i, 0 < I.w i) →
      ∀ (H : Finset (Fin n)) (Ll : List (Fin n)), Ll.Nodup → Ll.toFinset = light I H →
      ∀ (c : Fin n → ℝ) (W δ : ℝ), 0 < W → 0 < δ → δ ≤ 1 →
        ((∃ T' ⊆ light I H, W / (1 + δ) ≤ wsum I T' ∧ wsum I T' ≤ W) →
            ((knapsack I Ll c W δ).run 0).1.isSome) ∧
          (∀ T : List (Fin n), ((knapsack I Ll c W δ).run 0).1 = some T →
            T.Nodup ∧ T.toFinset ⊆ light I H ∧ InF I H δ W (H ∪ T.toFinset) ∧
              ∀ T' ⊆ light I H, W / (1 + δ) ≤ wsum I T' → wsum I T' ≤ W →
                ∑ i ∈ H ∪ T', c i ≤ ∑ i ∈ H ∪ T.toFinset, c i) ∧
          ((((knapsack I Ll c W δ).run 0).2 : ℝ) ≤ K * (n : ℝ) ^ 2 / δ) := by sorry

end MultiPurchaseMNL
