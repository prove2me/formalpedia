-- Prove2me | Theorems.Thm_NestedLogitVariants_PowersDelta_theorem_12
-- name    : NestedLogitVariants.PowersDelta.theorem_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:48:23.586985+00:00
-- url     : https://prove2.me/theorems/e6bc3a1a-956b-40f4-a0e4-f754409a6b3b
-- title:
--   Theorem 12, p. 28 — the powers-of-δ optimum of (4), scaled to (δ^(2γ̄+1) x̂, δ^(γ̄+1) ŷ), is feasible for (3)
-- statement:
--   Throughout, the instance satisfies the standing assumptions of §1, there is at least one product ($n \ge 1$), $\bar\gamma = \max_{i \in M} \gamma_i$ satisfies $\bar\gamma > 1$ (the standing assumption of §6, p. 25), and $\delta > 1$. Let $(\hat x, \hat y)$ be an optimal solution of problem (4) when the candidate collection of nest $i$ is $\{\hat S_{il} : l = l^L_i, \dots, l^U_i\} \cup \{\emptyset\}$, and the assortments $\hat S_{il}$ have the two properties of p. 28: whenever problem (15) at level $l$ is feasible, $\hat S_{il}$ is feasible for it and $\delta \sum_{j \in \hat S_{il}} r_{ij} v_{ij} \ge \hat G_{il}$. Then
--   $$\big(\delta^{2\bar\gamma + 1} \hat x,\ \delta^{\bar\gamma + 1} \hat y\big) \text{ is a feasible solution to problem (3)},$$
--   that is, $v_0\, \delta^{2\bar\gamma+1} \hat x \ge \sum_{i \in M} \delta^{\bar\gamma+1} \hat y_i$, and $\delta^{\bar\gamma+1} \hat y_i \ge V_i(S_i)^{\gamma_i} \big(R_i(S_i) - \delta^{2\bar\gamma+1} \hat x\big)$ for every nest $i$ and every assortment $S_i \subseteq N$.
--
--   Combined with Theorem 1, this shows that restricting nest $i$ to the at most $2 + \log_\delta(v^U_i / v^L_i)$ candidates $\{\hat S_{il}\} \cup \{\emptyset\}$ loses at most a factor $\delta^{2\bar\gamma+1}$ of the optimal expected revenue, for the general nested logit model with nest dissimilarity parameters above one and arbitrary nonnegative no-purchase weights in the nests.
--
--   **Formalization Note** The assortments $\hat S_{il}$ enter as an arbitrary family with the two properties of p. 28 (`IsPowersFamily`): the statement holds for every such family, which includes the one Proposition 15 constructs. A level with no feasible assortment imposes nothing on $\hat S_{il}$. Optimality of $(\hat x, \hat y)$ for (4) is feasibility plus minimality of $\hat x$ among feasible points. $\bar\gamma$ is passed as the greatest element of $\{\gamma_i\}$, so there is at least one nest. The pins of the shared model ($v_{ij} > 0$, $r_{ij} \ge 0$, $\gamma_i > 0$) are disclosed in the definition item.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 28, Theorem 12; proof in Appendix A.6, pp. 53–54

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

namespace NestedLogitVariants.PowersDelta

/-- Theorem 12, p. 28. Let `(x̂, ŷ)` be an optimal solution of problem (4) with the candidate
collections `{Ŝ_il : l = l^L_i, …, l^U_i} ∪ {∅}`. Then `(δ^{2γ̄+1} x̂, δ^{γ̄+1} ŷ)` is feasible for
problem (3), where `γ̄ = max_i γ_i > 1` and `δ > 1`. Stated for every family `Ŝ_il` with the two
properties of p. 28 (`IsPowersFamily`). -/
theorem theorem_12 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh) :
    LP3Feasible I (δ ^ (2 * γbar + 1) * xh) (δ ^ (γbar + 1) • yh) := by sorry

end NestedLogitVariants.PowersDelta
