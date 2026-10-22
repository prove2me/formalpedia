-- Prove2me | Theorems.Thm_JHolomorphic_tangent_isWeakJHolomorphicOn
-- name    : JHolomorphic.tangent_isWeakJHolomorphicOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:02:11.888204+00:00
-- url     : https://prove2.me/theorems/b5d6e4d8-3c7c-40da-ba58-3b6918ee9d0a
-- title:
--   A weakly $J$-holomorphic map is $J$-holomorphic, and $(u,\partial_s u)$ is weakly $J^T$-holomorphic
-- statement:
--   Let $p>2$, let $E$ be a finite-dimensional real normed space and let $J$ be a smooth almost complex structure on an open set $O\subseteq E$. Let $U\subseteq\mathbb{C}$ be open and let $u:U\to O$ be continuous, with $u\in W^{1,p}_{\mathrm{loc}}(U)$ and $\partial_su+J(u)\,\partial_tu=0$ almost everywhere on $U$ for its weak partial derivatives. Then:
--
--   1. $u$ is differentiable at every point of $U$ and $\partial_su+J(u)\,\partial_tu=0$ holds at every point of $U$ (classical derivatives);
--   2. the map $w(z)=(u(z),\partial_su(z))$ is continuous on $U$ with values in $O\times E$, lies in $W^{1,p}_{\mathrm{loc}}(U)$, and satisfies $\partial_sw+J^T(w)\,\partial_tw=0$ almost everywhere on $U$, where $J^T(x,y)(a,b)=\big(J(x)a,\;J(x)b+DJ(x)[y]\,a\big)$ is the tangent almost complex structure on $O\times E$.
--
--   **Formalization Note** The hypothesis is `IsWeakJHolomorphicOn p J O U u`. Conclusion 1 is `IsJHolomorphicOn J U u`; conclusion 2 is `IsWeakJHolomorphicOn p J^T (O ×ˢ Set.univ) U (fun z => (u z, fderiv ℝ u z 1))`, with $\partial_su(z)$ the classical derivative `fderiv ℝ u z 1` and $J^T$ written inline as `((J x.1).comp fst).prod ((J x.1).comp snd + (fderiv ℝ J x.1 x.2).comp fst)`. $E\times E$ carries the product norm. As in Wendl, the case $E=\mathbb{C}^n$ on a disc is the classical one; here the domain is any open $U$ and $J$ is only defined on $O$.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, §2.5 (regularity of $J$-holomorphic maps)

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory
open scoped ContDiff

/-- Let `p > 2` and let `J` be a smooth almost complex structure on an open set `O ⊆ E`. A
`W^{1,p}_loc` solution `u` of `∂ₛu + J(u) ∂ₜu = 0` on an open set `U ⊆ ℂ`, continuous with
values in `O`, is differentiable and `J`-holomorphic at every point of `U`, and the map
`z ↦ (u(z), ∂ₛu(z))` is a `W^{1,p}_loc` solution on `U` for the tangent almost complex structure
`J^T(x, y)(a, b) = (J(x) a, J(x) b + DJ(x)[y] a)` on `O × E`. -/
theorem tangent_isWeakJHolomorphicOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → E) (hu : IsWeakJHolomorphicOn p J O U u) :
    IsJHolomorphicOn J U u ∧
      IsWeakJHolomorphicOn p
        (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
          ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
            (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
        (O ×ˢ Set.univ) U (fun z => (u z, fderiv ℝ u z 1)) := by
  sorry

end JHolomorphic
