-- Prove2me | Theorems.Thm_JHolomorphic_fderiv_normed_convolution_eq_of_hasWeakPartialsOn
-- name    : JHolomorphic.fderiv_normed_convolution_eq_of_hasWeakPartialsOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T17:30:05.120497+00:00
-- url     : https://prove2.me/theorems/d4db5be4-b865-41e2-95c9-9aaadd400d0d
-- title:
--   Partial derivatives of a mollification are mollified weak partial derivatives
-- statement:
--   Let $E$ be a real Banach space, let $u:\mathbb{C}\to E$ be locally integrable, and let $u_s,u_t:\mathbb{C}\to E$ be weak partial derivatives of $u$ on all of $\mathbb{C}$. Let $\rho$ be a smooth bump function on $\mathbb{C}$ centred at $0$ and $\rho_1=\rho/\int\rho$ its normalisation. Then for every $z\in\mathbb{C}$
--
--   $$\partial_s(\rho_1*u)(z)=(\rho_1*u_s)(z),\qquad \partial_t(\rho_1*u)(z)=(\rho_1*u_t)(z),$$
--
--   with $z=s+it$ and $(\rho_1*f)(z)=\int\rho_1(t)\,f(z-t)\,dt$.
--
--   Mollification therefore commutes with weak differentiation, pointwise and without any integrability assumption on $u_s,u_t$ beyond the weak-derivative identities.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn Set.univ u us ut`, tested against real $C^\infty$ functions with compact support. $\partial_s$ is `fderiv ℝ · z 1` and $\partial_t$ is `fderiv ℝ · z Complex.I`. The bump function is a `ContDiffBump (0 : ℂ)`, its normalisation is `ρ.normed volume`, and the convolution is `⋆[lsmul ℝ ℝ, volume]`.
-- source:
--   Standard (elliptic regularity for the Cauchy–Riemann operator; weak derivatives and mollifiers).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace JHolomorphic

open MeasureTheory Filter Metric ContinuousLinearMap
open scoped ContDiff Convolution

/-- If `uₛ`, `uₜ` are weak partial derivatives on all of `ℂ` of a locally integrable
`u : ℂ → E`, then the partial derivatives of the mollification `ρ ⋆ u` are the
mollifications `ρ ⋆ uₛ` and `ρ ⋆ uₜ`. -/
theorem fderiv_normed_convolution_eq_of_hasWeakPartialsOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (ρ : ContDiffBump (0 : ℂ)) {u us ut : ℂ → E}
    (h : HasWeakPartialsOn Set.univ u us ut) (hu : LocallyIntegrable u volume) (z : ℂ) :
    fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z 1 =
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] us) z ∧
      fderiv ℝ (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] u) z Complex.I =
        (ρ.normed volume ⋆[lsmul ℝ ℝ, volume] ut) z := by
  sorry

end JHolomorphic
