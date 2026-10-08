-- Prove2me | Theorems.Thm_NestedLogitVariants_PowersDelta_xh_nonneg
-- name    : NestedLogitVariants.PowersDelta.xh_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:48:06.890443+00:00
-- url     : https://prove2.me/theorems/31a975ea-ff95-45d5-ae9e-2ec92bbbb347
-- title:
--   A.6, p. 53 — the optimal x̂ of (4) over the powers-of-δ candidates is nonnegative
-- statement:
--   Throughout, the instance satisfies the standing assumptions of §1, there is at least one product ($n \ge 1$), $\bar\gamma = \max_{i \in M} \gamma_i$ satisfies $\bar\gamma > 1$ (the standing assumption of §6, p. 25), and $\delta > 1$. Let $(\hat x, \hat y)$ be an optimal solution of problem (4) when the candidate collection of nest $i$ is $\{\hat S_{il} : l = l^L_i, \dots, l^U_i\} \cup \{\emptyset\}$, and the assortments $\hat S_{il}$ have the two properties of p. 28: whenever problem (15) at level $l$ is feasible, $\hat S_{il}$ is feasible for it and $\delta \sum_{j \in \hat S_{il}} r_{ij} v_{ij} \ge \hat G_{il}$. Then
--   $$\hat x \ge 0.$$
--
--   This is the first step of the proof of Theorem 12: it lets the factor $\delta^{2\bar\gamma+1}$ multiply $\hat x$ in an inequality without reversing it.
--
--   **Formalization Note** The assortments $\hat S_{il}$ enter as an arbitrary family with the two properties of p. 28 (`IsPowersFamily`): the statement holds for every such family, which includes the one Proposition 15 constructs. A level with no feasible assortment imposes nothing on $\hat S_{il}$. Optimality of $(\hat x, \hat y)$ for (4) is feasibility plus minimality of $\hat x$ among feasible points. $\bar\gamma$ is passed as the greatest element of $\{\gamma_i\}$, so there is at least one nest.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 53, Appendix A.6, first sentence of the proof of Theorem 12 (argument of the proof of Theorem 10, p. 45)

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Levels

namespace NestedLogitVariants.PowersDelta

/-- A.6, p. 53: "By using the same argument at the beginning of the proof of Theorem 10, it
follows that x̂ ≥ 0." Here `(x̂, ŷ)` is an optimal solution of (4) over the candidate collections
`{Ŝ_il : l = l^L_i, …, l^U_i} ∪ {∅}`. -/
theorem xh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n] (I : Instance ι n)
    (hI : I.Standing) (γbar : ℝ) (hγbar : IsGreatest (Set.range I.γ) γbar) (hγbar1 : 1 < γbar)
    (δ : ℝ) (hδ : 1 < δ)
    (Sh : ι → ℤ → Finset (Fin n)) (hSh : IsPowersFamily I δ Sh)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (powersCandidates I δ Sh) xh yh) :
    0 ≤ xh := by sorry

end NestedLogitVariants.PowersDelta
