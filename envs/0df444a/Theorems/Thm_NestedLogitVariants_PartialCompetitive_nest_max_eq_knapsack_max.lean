-- Prove2me | Theorems.Thm_NestedLogitVariants_PartialCompetitive_nest_max_eq_knapsack_max
-- name    : NestedLogitVariants.PartialCompetitive.nest_max_eq_knapsack_max
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:07:33.962026+00:00
-- url     : https://prove2.me/theorems/7839b25b-7e0f-4045-bda1-b990ca607690
-- title:
--   Proof of Lemma 9, p. 23 — for x ≥ 0, max_S V_i(S)^γ_i (R_i(S) − x) equals max_{ϵ≥0} (v_i0+ϵ)^γ_i [K_i(ϵ)/(v_i0+ϵ) − x]
-- statement:
--   Consider a nested logit instance in which every dissimilarity parameter satisfies $\gamma_i \le 1$, fix a nest $i$ and a number $x \ge 0$, and let $K_i(\epsilon)$ be the knapsack value of display (9). Then
--
--   $$\max_{S_i \subseteq N} V_i(S_i)^{\gamma_i}\big(R_i(S_i) - x\big) = \max_{\epsilon_i \ge 0} \Big\{ (v_{i0} + \epsilon_i)^{\gamma_i} \Big[ \frac{K_i(\epsilon_i)}{v_{i0} + \epsilon_i} - x \Big] \Big\}.$$
--
--   Equivalently, a number $y$ satisfies $y \ge V_i(S_i)^{\gamma_i}(R_i(S_i) - x)$ for every assortment $S_i \subseteq N$ if and only if $y \ge (v_{i0} + \epsilon)^{\gamma_i}[K_i(\epsilon)/(v_{i0}+\epsilon) - x]$ for every $\epsilon \ge 0$.
--
--   This identity turns the per-nest constraint of the linear program (3), one inequality per assortment, into a constraint indexed by a single capacity parameter, and is the core of Lemma 9.
--
--   **Formalization Note** Both maxima are attained (the left one over a finite family; the right one at a capacity equal to the weight of a knapsack-optimal assortment), so the equality of the two maxima is stated as: $y$ bounds one family if and only if it bounds the other, without forming a real supremum. The hypothesis $x \ge 0$ is the page's; for $x < 0$ the right-hand family is unbounded.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 23, proof of Lemma 9, first display

import Mathlib
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Model
import Definitions.Def_NestedLogitVariants_PartialCompetitive_Knapsack

namespace NestedLogitVariants.PartialCompetitive

/-- Proof of Lemma 9, p. 23. For `x ≥ 0` and dissimilarity parameters at most one, the two maxima
`max_{S ⊂ N} V_i(S)^{γ_i} (R_i(S) − x)` and `max_{ε ≥ 0} (v_{i0} + ε)^{γ_i} [K_i(ε)/(v_{i0} + ε) − x]`
coincide; stated as: a number `y` bounds the first family iff it bounds the second. -/
theorem nest_max_eq_knapsack_max {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hγ : ∀ i, I.γ i ≤ 1) (i : ι) (x : ℝ) (hx : 0 ≤ x) (y : ℝ) :
    (∀ S : Finset (Fin n), nestWeight I i S * (R I i S - x) ≤ y) ↔
      (∀ ε : ℝ, 0 ≤ ε → (I.vnp i + ε) ^ I.γ i * (Kval I i ε / (I.vnp i + ε) - x) ≤ y) := by sorry

end NestedLogitVariants.PartialCompetitive
