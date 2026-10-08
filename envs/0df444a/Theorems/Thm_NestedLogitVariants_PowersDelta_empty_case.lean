-- Prove2me | Theorems.Thm_NestedLogitVariants_PowersDelta_empty_case
-- name    : NestedLogitVariants.PowersDelta.empty_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:48:18.974324+00:00
-- url     : https://prove2.me/theorems/35968549-9cd0-4407-b88f-e8704bd6c1da
-- title:
--   A.6, p. 54 — the scaled solution satisfies the constraint of (3) for the empty assortment
-- statement:
--   Throughout, the instance satisfies the standing assumptions of §1, there is at least one product ($n \ge 1$), $\bar\gamma = \max_{i \in M} \gamma_i$ satisfies $\bar\gamma > 1$ (the standing assumption of §6, p. 25), and $\delta > 1$. Let $(\hat x, \hat y)$ be an optimal solution of problem (4) when the candidate collection of nest $i$ is $\{\hat S_{il} : l = l^L_i, \dots, l^U_i\} \cup \{\emptyset\}$, and the assortments $\hat S_{il}$ have the two properties of p. 28: whenever problem (15) at level $l$ is feasible, $\hat S_{il}$ is feasible for it and $\delta \sum_{j \in \hat S_{il}} r_{ij} v_{ij} \ge \hat G_{il}$. Then for every nest $i$,
--   $$\delta^{\bar\gamma + 1} \hat y_i \ge V_i(\emptyset)^{\gamma_i} \big( R_i(\emptyset) - \delta^{2\bar\gamma + 1} \hat x \big).$$
--
--   This is the second case of the proof of Theorem 12. Here $R_i(\emptyset) = 0$ and $V_i(\emptyset) = v_{i0}$.
--
--   **Formalization Note** The assortments $\hat S_{il}$ enter as an arbitrary family with the two properties of p. 28 (`IsPowersFamily`): the statement holds for every such family, which includes the one Proposition 15 constructs. A level with no feasible assortment imposes nothing on $\hat S_{il}$. Optimality of $(\hat x, \hat y)$ for (4) is feasibility plus minimality of $\hat x$ among feasible points. $\bar\gamma$ is passed as the greatest element of $\{\gamma_i\}$, so there is at least one nest.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 54, Appendix A.6, second case (S_i = ∅)

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

namespace NestedLogitVariants.PowersDelta

/-- A.6, p. 54: for the empty assortment of nest `i`,
`δ^{γ̄+1} ŷ_i ≥ V_i(∅)^{γ_i} (R_i(∅) − δ^{2γ̄+1} x̂)`. -/
theorem empty_case {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh)
    (i : ι) :
    nestWeight I i ∅ * (R I i ∅ - δ ^ (2 * γbar + 1) * xh) ≤ δ ^ (γbar + 1) * yh i := by sorry

end NestedLogitVariants.PowersDelta
