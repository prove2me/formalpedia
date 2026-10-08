-- Prove2me | Theorems.Thm_NestedLogitVariants_PowersDelta_exists_level
-- name    : NestedLogitVariants.PowersDelta.exists_level
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:48:01.172037+00:00
-- url     : https://prove2.me/theorems/66eb5f55-cd06-4c0f-9b76-4ec4e2942d8f
-- title:
--   p. 28 and A.6, p. 53 — every nonempty assortment of nest i lies in some level l = l^L_i, …, l^U_i
-- statement:
--   Throughout, the instance satisfies the standing assumptions of §1, there is at least one product ($n \ge 1$), $\bar\gamma = \max_{i \in M} \gamma_i$ satisfies $\bar\gamma > 1$ (the standing assumption of §6, p. 25), and $\delta > 1$. For every nest $i$ and every nonempty assortment $S \subseteq N$ there is an integer $l$ with $l^L_i \le l \le l^U_i$ and
--   $$\delta^{l-1} \le v_{i0} + \sum_{j \in S} v_{ij} \le \delta^l.$$
--
--   This is the inclusion $[v^L_i, v^U_i] \subset [\delta^{l^L_i - 1}, \delta^{l^U_i}]$ of p. 28, used in the proof of Theorem 12 to attach to an arbitrary assortment the level whose candidate $\hat S_{il}$ it is compared with.
--
--   **Formalization Note** $l^L_i$, $l^U_i$ are the ceilings of $\log_\delta v^L_i$, $\log_\delta v^U_i$ (see the definition item). The section's standing assumption $\bar\gamma > 1$ is carried for uniformity with the other statements; it is not used here.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 28, §6.2 (definition of l^L_i, l^U_i) and p. 53, Appendix A.6 (choice of l)

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

namespace NestedLogitVariants.PowersDelta

/-- p. 28 and A.6, p. 53: every nonempty assortment `S` of nest `i` lies in a level
`l ∈ {l^L_i, …, l^U_i}`, i.e. `δ^{l−1} ≤ v_{i0} + ∑_{j∈S} v_{ij} ≤ δ^l`; this is the inclusion
`[v^L_i, v^U_i] ⊂ [δ^{l^L_i − 1}, δ^{l^U_i}]`. -/
theorem exists_level {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (i : ι) (S : Finset (Fin n)) (hS : S.Nonempty) :
    ∃ l : ℤ, lL I i δ ≤ l ∧ l ≤ lU I i δ ∧ InLevel I i δ l S := by sorry

end NestedLogitVariants.PowersDelta
