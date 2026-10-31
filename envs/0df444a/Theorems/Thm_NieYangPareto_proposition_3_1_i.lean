-- Prove2me | Theorems.Thm_NieYangPareto_proposition_3_1_i
-- name    : NieYangPareto.proposition_3_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:03:36.940535+00:00
-- url     : https://prove2.me/theorems/2d510763-ce03-452d-a479-33183b123a7b
-- title:
--   Proposition 3.1(i) — WPV iff on the boundary of $\mathcal U$; an extreme point of $\operatorname{conv}(\mathcal U)$ is a PV
-- statement:
--   Let $\mathcal U$ be as in (3.1), and let $v\in f(K)$. Then:
--
--   1. $v$ is a weakly Pareto value if and only if $v$ lies on the boundary of $\mathcal U$;
--   2. if $v$ is an extreme point of $\operatorname{conv}(\mathcal U)$, then $v$ is a Pareto value.
--
--   This is the geometric form of the weakly Pareto condition, which Theorem 3.2 transfers to $\operatorname{cl}(\mathcal V)$.
--
--   Differences from the source:
--   - encoding: disjoint finite label sets ℰ, ℐ → two finite types E, I (`[Finite E] [Finite I]`), each with its own constraint family; reason: separate types encode disjointness; the same instances
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, Proposition 3.1(i), p.6

import Mathlib
import Definitions.Def_NieYangPareto_MOP
import Definitions.Def_NieYangPareto_ParetoNotions
import Definitions.Def_NieYangPareto_MOP_U

namespace NieYangPareto

/-- **Proposition 3.1(i).** Nie–Yang, arXiv:2108.04336v2, Proposition 3.1(i), p.6: for each
`v ∈ f(K)`, the vector `v` is a WPV if and only if `v` lies on the boundary of `𝒰`. Moreover, if `v`
is an extreme point of `conv(𝒰)`, then `v` is a PV. -/
theorem proposition_3_1_i {n m : ℕ} {E I : Type*} [Finite E] [Finite I]
    (P : MOP n m E I)
    (v : Fin m → ℝ) (hv : v ∈ P.obj '' P.K) :
    (P.IsWeaklyParetoValue v ↔ v ∈ frontier P.U) ∧
      (v ∈ (convexHull ℝ P.U).extremePoints ℝ → P.IsParetoValue v) := by sorry

end NieYangPareto
