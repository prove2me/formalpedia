-- Prove2me | Theorems.Thm_JHolomorphic_isJHolomorphicOn_tangent
-- name    : JHolomorphic.isJHolomorphicOn_tangent
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T22:25:54.624835+00:00
-- url     : https://prove2.me/theorems/8f453172-49fc-4247-ad23-30c5b9701135
-- title:
--   The tangent lift of a pseudoholomorphic map is pseudoholomorphic
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $O\subseteq E$ open and $J$ a smooth almost complex structure on $O$. Its tangent structure on $O\times E$ is
--   $$J^T(x,y)(a,b)=\bigl(J(x)a,\ J(x)b+DJ(x)[y]\,a\bigr).$$
--   Let $U\subseteq\mathbb{C}$ be open and $u:U\to O$ a $C^2$ map with $\partial_su+J(u)\,\partial_tu=0$ on $U$. Then for every $e\in\mathbb{C}$ the map $z\mapsto\bigl(u(z),Du(z)e\bigr)$ is $J^T$-holomorphic on $U$. For $e=1$ and $e=i$ these are the lifts $(u,\partial_su)$ and $(u,\partial_tu)$.
--
--   **Formalization Note** $J^T$ is written inline as the map `fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) + (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E))`, which is defined on all of $E\times E$. The hypotheses are `IsAlmostComplexOn J O`, `IsOpen U`, `ContDiffOn ℝ 2 u U`, `IsJHolomorphicOn J U u` and `Set.MapsTo u U O`; the conclusion is `IsJHolomorphicOn` for $J^T$ on `U` of `fun z => (u z, fderiv ℝ u z e)`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, proof of Theorem 2.22

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal NNReal

/-- The tangent lift of a pseudoholomorphic map: if `u` is a `C²` `J`-holomorphic map on an open
set `U ⊆ ℂ` with values in `O`, where `J` is a smooth almost complex structure on `O`, then for
every direction `e ∈ ℂ` the map `z ↦ (u(z), Du(z) e)` is holomorphic for the tangent structure
`J^T(x, y)(a, b) = (J(x) a, J(x) b + DJ(x)[y] a)` on `O × E`. -/
theorem isJHolomorphicOn_tangent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U) (u : ℂ → E)
    (hu : ContDiffOn ℝ 2 u U) (hhol : IsJHolomorphicOn J U u) (hmaps : Set.MapsTo u U O)
    (e : ℂ) :
    IsJHolomorphicOn
      (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      U (fun z => (u z, fderiv ℝ u z e)) := by
  sorry

end JHolomorphic
