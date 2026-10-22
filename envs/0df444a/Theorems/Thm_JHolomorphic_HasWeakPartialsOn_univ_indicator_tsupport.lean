-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_univ_indicator_tsupport
-- name    : JHolomorphic.HasWeakPartialsOn.univ_indicator_tsupport
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T17:30:09.217635+00:00
-- url     : https://prove2.me/theorems/d0ead9cf-bca1-45d7-8472-8fd985ac9c45
-- title:
--   Weak partial derivatives of a compactly supported map extend by zero to all of $\mathbb{C}$
-- statement:
--   Let $E$ be a finite-dimensional real normed space, let $U\subseteq\mathbb{C}$ be open, and let $1\le p\le\infty$. Let $\xi:\mathbb{C}\to E$ be continuous with compact support $K=\operatorname{tsupport}\xi\subseteq U$, and suppose $\xi$ has weak partial derivatives $\xi_s,\xi_t$ on $U$ with $\xi_s,\xi_t\in L^p(U)$. Then:
--
--   1. the maps $\mathbf 1_K\xi_s$ and $\mathbf 1_K\xi_t$ (equal to $\xi_s$, $\xi_t$ on $K$ and to $0$ elsewhere) are weak partial derivatives of $\xi$ on all of $\mathbb{C}$;
--   2. $\xi_s=\mathbf 1_K\xi_s$ and $\xi_t=\mathbf 1_K\xi_t$ almost everywhere on $U$; equivalently, $\xi_s$ and $\xi_t$ vanish almost everywhere on $U\setminus K$.
--
--   This lets a compactly supported $W^{1,p}$ map on an open set be treated as a $W^{1,p}$ map on the whole plane.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn`, tested against real $C^\infty$ functions with compact support in the given open set; $\partial_s$ is the derivative in direction $1$ and $\partial_t$ in direction $i$. $p$ is an `ENNReal`; $L^p(U)$ membership is `MemLp` for Lebesgue measure restricted to $U$. The support $K$ is the closed support `tsupport ξ`, and $\mathbf 1_K f$ is `(tsupport ξ).indicator f`.
-- source:
--   Standard (elliptic regularity for the Cauchy–Riemann operator; weak derivatives and mollifiers).

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_local
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_congr_ae

namespace JHolomorphic

open MeasureTheory Filter
open scoped ContDiff ENNReal

/-- A map with compact support `K ⊆ U` whose weak partials on the open set `U` lie in `L^p(U)`
(`1 ≤ p`) has, on all of `ℂ`, the weak partials obtained by restricting them to `K` and extending
by zero; moreover the given partials vanish almost everywhere on `U \ K`. -/
theorem HasWeakPartialsOn.univ_indicator_tsupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {ξ ξs ξt : ℂ → E} (hξ : Continuous ξ) (hc : HasCompactSupport ξ)
    (hsub : tsupport ξ ⊆ U) (h : HasWeakPartialsOn U ξ ξs ξt)
    (hs : MemLp ξs p (volume.restrict U)) (ht : MemLp ξt p (volume.restrict U)) :
    HasWeakPartialsOn Set.univ ξ ((tsupport ξ).indicator ξs) ((tsupport ξ).indicator ξt) ∧
      ∀ᵐ z ∂(volume.restrict U),
        ξs z = (tsupport ξ).indicator ξs z ∧ ξt z = (tsupport ξ).indicator ξt z := by
  sorry

end JHolomorphic
