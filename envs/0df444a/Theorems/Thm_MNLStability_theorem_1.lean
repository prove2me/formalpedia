-- Prove2me | Theorems.Thm_MNLStability_theorem_1
-- name    : MNLStability.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:56.158404+00:00
-- url     : https://prove2.me/theorems/f694754d-e8b8-4191-82d7-d2daca077693
-- title:
--   Theorem 1 — a randomized $(1-\varepsilon)$-approximation scheme for dynamic assortment planning (corrected: $1+\log\Delta$ and a factor $L_M$)
-- statement:
--   There are absolute constants $c_1,c_2>0$ such that the following holds for the program `ptas`. Take any valid instance of dynamic assortment planning under the Multinomial Logit choice model: $n\ge1$ products with positive preference weights $w_i$ and non-negative prices $r_i$, a no-purchase weight $w_0>0$, a capacity $C\ge1$, and a finitely supported law of the number of customers $M$. Let $\Delta=w_{\max}/w_{\min}$ and let $L_M=\sum_{m\in\operatorname{supp}M}(1+\lfloor\log_2(m+1)\rfloor)$ be the bit length of the support of $M$. For every accuracy level $\varepsilon>0$ and every confidence level $\delta\in(0,1)$:
--
--   1. with probability at least $1-\delta$ over the program's randomness, the returned vector $\hat U$ satisfies
--   $$\mathbb E[R(\hat U)]\ \ge\ (1-\varepsilon)\cdot\max\Bigl\{\mathbb E[R(U)]:\ \sum_iU_i\le C\Bigr\};$$
--   2. every run returns a feasible vector, $\sum_i\hat U_i\le C$;
--   3. every run costs at most
--   $$c_1\cdot\frac1\delta\cdot L_M\cdot(nC)^{c_2(1+\log\Delta)/\varepsilon^3}$$
--   unit operations.
--
--   The paper's statement: "For any accuracy level $\varepsilon>0$ and confidence level $\delta\in(0,1)$, the dynamic assortment planning problem under the Multinomial Logit choice model can be approximated within factor $1-\varepsilon$. The running time of our randomized algorithm is $O(\frac1\delta\cdot(nC)^{O(\log\Delta/\varepsilon^3)})$ and its success probability is at least $1-\delta$." It is the first approximation scheme for joint assortment and inventory planning under dynamic MNL substitution, and it is polynomial when the weights are within a constant factor of each other.
--
--   Differences from the source:
--   - correction: running time O((1/δ)·(nC)^{O(log Δ/ε³)}) → exponent c₂(1 + log Δ)/ε³; reason: with one constant the printed exponent is 0 at Δ = 1, giving time O(1/δ) independent of n and C; but with all weights 1, w₀ = 1, C = 1, M ≡ 1 and price 1 on one unknown product (0 elsewhere), only vectors stocking that product are (1 − ε)-optimal for ε < 1, so Ω(n) prices must be read
--   - correction: running time with no term for the law of M → an extra factor L_M, the bit length of the support of M; reason: the law is part of the input (p.3); with n = 2, C = 1, ε = 1/10, δ = 1/2, Δ = 9 fixed, two laws differing in one support atom of mass 1/s (a huge value) reverse which product is optimal by a factor 3, so Ω(s) reads are needed
--   - generalization: "our randomized algorithm" (an existential claim) → the named program ptas; reason: the program witnesses the existence
--   - reading: running time in an unspecified model → unit-cost real RAM: one unit per arithmetic operation, comparison, ⌊·⌋, ⌈·⌉, log, list access and loop dispatch, a geometric draw at cost 1, a categorical draw over ℓ masses at cost ℓ + 1; reason: the paper fixes no model; the geometric draw makes a simulated run independent of the value of M, as the cited oracle requires
--   - reading: "can be approximated within factor 1 − ε … success probability at least 1 − δ" → Pr[(1 − ε)·OPT ≤ E[R(Û)]] ≥ 1 − δ over the program's randomness, E[R(Û)] the expected revenue of the returned vector; feasibility on every run; reason: the guarantee §3.3–3.4 prove
--   - encoding: an instance (§1.1) → n ≥ 1, C ≥ 1, w₀ > 0, wᵢ > 0, rᵢ ≥ 0, M finitely supported with an explicit law; reason: preference weights, selling prices and a finite support (p.3); n = 0 or C = 0 make the bound 0
--   - encoding: O(·) → absolute constants c₁, c₂ chosen before the instance, ε and δ; the cost bound on every run; reason: the usual reading of O(·)
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Theorem 1, pp.5–6; proof §3, pp.14–18; Δ defined p.5

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_Inst
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_ptas

namespace MNLStability

/-- **Theorem 1** (SSRN:3498325, pp.5–6; proof §3, pp.14–18), for the explicit program `ptas`.
There are absolute constants `c₁, c₂ > 0` such that, for every valid instance of dynamic assortment
planning under the MNL choice model (`n ≥ 1` products, capacity `C ≥ 1`, positive weights,
non-negative prices, a finitely supported law of the number of customers `M`), every accuracy level
`ε > 0` and every confidence level `δ ∈ (0, 1)`:
1. with probability at least `1 − δ`, the returned vector `Û` satisfies `E[R(Û)] ≥ (1 − ε)·OPT`;
2. every run returns a feasible vector, `Σ_i Û_i ≤ C`;
3. every run costs at most `c₁·δ⁻¹·L_M·(nC)^{c₂(1 + log Δ)/ε³}` unit operations, where
   `Δ = w_max/w_min` and `L_M` is the bit length of the support of `M`. -/
theorem theorem_1 : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n : ℕ) (I : Inst n), I.Valid → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → δ < 1 →
      1 - δ ≤ (((ptas I ε δ).run 0).toOuterMeasure
          {x | (1 - ε) * opt I ≤ expR I.wts I.r I.pM x.1}).toReal ∧
      ∀ x ∈ ((ptas I ε δ).run 0).support,
        norm1 x.1 ≤ I.C ∧
        (x.2 : ℝ) ≤ c₁ * δ⁻¹ * LM I.pM *
          ((n * I.C : ℕ) : ℝ) ^ (c₂ * (1 + Real.log I.wts.Delta) / ε ^ 3) := by sorry

end MNLStability
