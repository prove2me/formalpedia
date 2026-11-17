-- Prove2me | Theorems.Thm_GSRandomOrder_Supplement_theorem_4_1
-- name    : GSRandomOrder.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:11:17.48719+00:00
-- url     : https://prove2.me/theorems/e2c0f9e9-d171-419e-829b-e588a56580e1
-- title:
--   Theorem 4.1 — welfare $\frac{3-2\sqrt2}{e}\,\mathrm{OPT}$ by frozen routing with $\lambda=\sqrt2-1$
-- statement:
--   Let $v_1,\dots,v_m$ be GS valuations on the item set $N=\{1,\dots,n\}$, with values in $\mathbb R\cup\{-\infty\}$ and $v_i(\emptyset)=0$ (signed, possibly $-\infty$, not necessarily monotone), and let the items arrive in uniformly random order. Run **frozen routing** (Section 4.2) with $\lambda=\sqrt2-1$, any order $\prec$ on the labels and any tie-breaking order on the bidders, and let $A_i$ be the bundle of bidder $i$. Then
--   $$
--   \mathbb E\sum_{i=1}^m v_i(A_i)\ \ge\ \frac{3-2\sqrt2}{e}\,\mathrm{OPT}\ \approx\ 0.0631\,\mathrm{OPT},
--   $$
--   where $\mathrm{OPT}=W(N)$ is the optimal welfare (2), and $v_i(A_i)\ge0$ for every bidder at every time.
--
--   This is the paper's constant-factor guarantee for online welfare maximization with signed GS bidders in random order (Theorem B); the constant comes from optimizing $\lambda(1-\lambda)/(1+\lambda)$ over the coin bias.
--
--   **Formalization Note** The randomness consists of independent uniform heads variables, arrival times and acceptance coins. The nonnegativity clause is stated on every sample point and at every real time $s$; the expectation reads $v_i(A_i)$ at time $1$ as a real number.
--
--   Differences from the source:
--   - encoding: K ∼ Bin(n, λ), the first K arrivals discarded, sorted uniforms attached to the other arrivals → independent heads coins h_g < λ and independent uniform times r_g for every item (the times of heads items are not read); reason: the paper notes (p.12) that this gives the same joint law of L and (t_g)_{g∉L}
--   - encoding: a total order ≺ on labels and a tie-breaking order on bidders → arbitrary bijections π : Fin n ≃ Fin n and ρ : Fin m ≃ Fin m (k-th label, k-th bidder), both universally quantified; reason: a total order on a finite set is the same as an enumeration
--   - encoding: v_i(A_i) ≥ 0 for every bidder at every time → 0 ≤ v_i(A_i(s)) for every sample point and every real time s; reason: the printed clause has no "almost surely"; stated on every path
--   - encoding: E Σ v_i(A_i) with ≈ 0.0631 OPT → Bochner integral of Σ_i (v_i(A_i)).unbotD 0 at time 1; the numerical approximation is not stated; reason: v_i(A_i) ≥ 0 makes unbotD exact; 0.0631 is an approximation of the exact constant (3 − 2√2)/e, not a separate claim
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §4, p.11, Theorem 4.1 (= Theorem B, p.4); frozen routing §4.2, pp.12–13

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_runSurvival
import Definitions.Def_GSRandomOrder_Supplement_welfare
import Definitions.Def_GSRandomOrder_Supplement_frozenRouting

set_option autoImplicit false

open MeasureTheory

namespace GSRandomOrder.Supplement

/-- **Theorem 4.1 (Welfare)** (R. Paes Leme, M. Pál, N. Patel, *Gross Substitutes Welfare in
Random Order*, STOC 2027 submission, manuscript sha256 69787f50…, §4, p.11; = Theorem B, p.4).
Let `v_1, …, v_m` be GS valuations on `N`, with values in `ℝ ∪ {−∞}` and `v_i(∅) = 0`, and let the
items arrive in uniformly random order. Frozen routing (Section 4.2) with `λ = √2 − 1` obtains
`E Σ_{i=1}^m v_i(A_i) ≥ ((3 − 2√2)/e) OPT ≈ 0.0631 OPT`, and `v_i(A_i) ≥ 0` for every bidder at
every time.

**Formalization Note.**
* Frozen routing is `frozenRouting` with `λ = √2 − 1`, an arbitrary label order `π` and an
  arbitrary bidder tie-breaking order `ρ` (both quantified); the randomness is `FRΩ n` with
  `volume`: independent uniform heads coins, arrival times and acceptance coins (the paper's
  binomial/sorted-uniform construction gives the same joint law, see `frozenRouting`).
* "At every time" is stated on every sample point and at every real time `s`.
* `OPT = W(N)` is `welfare v univ`; `A_i` is the bundle at time `1` (all items have arrived);
  `v_i(A_i)` is read as a real with `unbotD 0`, exact by the first clause; `e = Real.exp 1`. -/
theorem theorem_4_1 {n m : ℕ} (v : Fin m → Finset (Fin n) → WithBot ℝ)
    (hv : ∀ i, IsGSValuation (v i)) (π : Fin n ≃ Fin n) (ρ : Fin m ≃ Fin m) :
    (∀ x : FRΩ n, ∀ s : ℝ, ∀ i : Fin m,
      0 ≤ v i (frozenRouting v π ρ (Real.sqrt 2 - 1) x s i)) ∧
    (3 - 2 * Real.sqrt 2) / Real.exp 1 * welfare v Finset.univ ≤
      ∫ x : FRΩ n, ∑ i : Fin m, (v i (frozenRouting v π ρ (Real.sqrt 2 - 1) x 1 i)).unbotD 0 := by sorry

end GSRandomOrder.Supplement
