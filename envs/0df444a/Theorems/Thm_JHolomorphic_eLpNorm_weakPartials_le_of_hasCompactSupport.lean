-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_weakPartials_le_of_hasCompactSupport
-- name    : JHolomorphic.eLpNorm_weakPartials_le_of_hasCompactSupport
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T15:56:16.295074+00:00
-- url     : https://prove2.me/theorems/d38b910f-704d-490d-8e7d-2aa65da0c7cc
-- title:
--   An $L^p$ estimate for $\partial_s+J_0\partial_t$ on compactly supported maps from planar domains
-- statement:
--   Let $1<p<\infty$, let $E$ be a finite-dimensional real normed space and let $J_0:E\to E$ be a real linear map with $J_0^2=-1$. There is a constant $C$ with the following property. Let $U\subseteq\mathbb{C}$ be open and let $\xi:\mathbb{C}\to E$ be continuous with compact support contained in $U$, with weak partial derivatives $\xi_s,\xi_t$ on $U$ lying in $L^p(U)$. Then
--   $$\|\xi_s\|_{L^p(U)}+\|\xi_t\|_{L^p(U)}\le C\,\|\xi_s+J_0\,\xi_t\|_{L^p(U)}.$$
--   This is the $L^p$ estimate for the constant-coefficient Cauchy–Riemann type operator $\partial_s+J_0\partial_t$, used in the local regularity theory of pseudoholomorphic maps.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn`, tested against real $C^\infty$ functions with compact support in $U$; $\xi_s$ is the derivative in the direction $1$ and $\xi_t$ in the direction $i$. The norms are `eLpNorm _ (ENNReal.ofReal p)` for the Lebesgue measure restricted to $U$. The constant $C$ depends only on $p$, $E$ and $J_0$, not on $U$ or $\xi$.
-- source:
--   Standard; see C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2 (estimates for the linear Cauchy–Riemann operator), and D. McDuff, D. Salamon, J-holomorphic Curves and Symplectic Topology, Appendix B

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric
open scoped ContDiff

/-- Let `1 < p < ∞` and let `J₀` be a complex structure on the finite-dimensional real space `E`
(`J₀ ∘ J₀ = -1`). There is a constant `C` such that for every open `U ⊆ ℂ` and every continuous
`ξ : ℂ → E` with compact support in `U` whose weak partials `ξₛ`, `ξₜ` on `U` lie in `L^p(U)`,
`‖ξₛ‖_{L^p(U)} + ‖ξₜ‖_{L^p(U)} ≤ C ‖ξₛ + J₀ ξₜ‖_{L^p(U)}`. -/
theorem eLpNorm_weakPartials_le_of_hasCompactSupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (J₀ : E →L[ℝ] E)
    (hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ U : Set ℂ, IsOpen U → ∀ ξ ξs ξt : ℂ → E, Continuous ξ → HasCompactSupport ξ →
      tsupport ξ ⊆ U → HasWeakPartialsOn U ξ ξs ξt →
      MemLp ξs (ENNReal.ofReal p) (volume.restrict U) →
      MemLp ξt (ENNReal.ofReal p) (volume.restrict U) →
      eLpNorm ξs (ENNReal.ofReal p) (volume.restrict U) +
          eLpNorm ξt (ENNReal.ofReal p) (volume.restrict U) ≤
        ENNReal.ofReal C * eLpNorm (fun z => ξs z + J₀ (ξt z)) (ENNReal.ofReal p)
          (volume.restrict U) := by
  sorry

end JHolomorphic
