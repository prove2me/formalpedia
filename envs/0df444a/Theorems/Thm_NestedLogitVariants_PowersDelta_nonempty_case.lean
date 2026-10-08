-- Prove2me | Theorems.Thm_NestedLogitVariants_PowersDelta_nonempty_case
-- name    : NestedLogitVariants.PowersDelta.nonempty_case
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:48:21.093205+00:00
-- url     : https://prove2.me/theorems/2482132f-0b61-4b6e-89a3-46eeea65dd99
-- title:
--   A.6, pp. 53–54 — the scaled solution satisfies the constraint of (3) for every nonempty assortment
-- statement:
--   Throughout, the instance satisfies the standing assumptions of §1, there is at least one product ($n \ge 1$), $\bar\gamma = \max_{i \in M} \gamma_i$ satisfies $\bar\gamma > 1$ (the standing assumption of §6, p. 25), and $\delta > 1$. Let $(\hat x, \hat y)$ be an optimal solution of problem (4) when the candidate collection of nest $i$ is $\{\hat S_{il} : l = l^L_i, \dots, l^U_i\} \cup \{\emptyset\}$, and the assortments $\hat S_{il}$ have the two properties of p. 28: whenever problem (15) at level $l$ is feasible, $\hat S_{il}$ is feasible for it and $\delta \sum_{j \in \hat S_{il}} r_{ij} v_{ij} \ge \hat G_{il}$. Then for every nest $i$ and every nonempty assortment $S \subseteq N$,
--   $$\delta^{\bar\gamma + 1} \hat y_i \ge V_i(S)^{\gamma_i} \big( R_i(S) - \delta^{2\bar\gamma + 1} \hat x \big).$$
--
--   This is the nonempty case of the proof of Theorem 12: the scaled pair $(\delta^{2\bar\gamma+1} \hat x, \delta^{\bar\gamma+1} \hat y)$ satisfies the second family of constraints of problem (3) at every nonempty assortment. Its proof uses display (35), $\delta \sum_{j \in \hat S_{il}} r_{ij} v_{ij} \ge \hat G_{il} \ge \sum_{j \in S_i} r_{ij} v_{ij}$, which is the defining property of $\hat S_{il}$.
--
--   **Formalization Note** The assortments $\hat S_{il}$ enter as an arbitrary family with the two properties of p. 28 (`IsPowersFamily`): the statement holds for every such family, which includes the one Proposition 15 constructs. A level with no feasible assortment imposes nothing on $\hat S_{il}$. Optimality of $(\hat x, \hat y)$ for (4) is feasibility plus minimality of $\hat x$ among feasible points. $\bar\gamma$ is passed as the greatest element of $\{\gamma_i\}$, so there is at least one nest.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 53–54, Appendix A.6, first case (S_i ≠ ∅), displays (34)–(36)

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

namespace NestedLogitVariants.PowersDelta

/-- A.6, pp. 53–54: for a nonempty assortment `S` of nest `i`,
`δ^{γ̄+1} ŷ_i ≥ V_i(S)^{γ_i} (R_i(S) − δ^{2γ̄+1} x̂)`. -/
theorem nonempty_case {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh)
    (i : ι) (S : Finset (Fin n)) (hS : S.Nonempty) :
    nestWeight I i S * (R I i S - δ ^ (2 * γbar + 1) * xh) ≤ δ ^ (γbar + 1) * yh i := by sorry

end NestedLogitVariants.PowersDelta
