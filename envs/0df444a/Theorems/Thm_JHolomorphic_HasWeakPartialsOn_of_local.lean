-- Prove2me | Theorems.Thm_JHolomorphic_HasWeakPartialsOn_of_local
-- name    : JHolomorphic.HasWeakPartialsOn.of_local
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T14:22:25.037765+00:00
-- url     : https://prove2.me/theorems/037357e8-14b3-4bb6-b667-0828490fa147
-- title:
--   Local weak partial derivatives in $L^p$ glue to weak partial derivatives in $L^p_{\mathrm{loc}}$
-- statement:
--   Let $E$ be a finite-dimensional real normed space, let $U\subseteq\mathbb{C}$ be open, let $1\le p\le\infty$, and let $f:\mathbb{C}\to E$ be integrable on every compact subset of $U$. Suppose every $z\in U$ has an open neighbourhood $V\subseteq U$ on which $f$ has weak partial derivatives $g_s^V,g_t^V\in L^p(V)$. Then there are $g_s,g_t:\mathbb{C}\to E$ such that
--
--   $$\int \partial_s\varphi\, f=-\int \varphi\, g_s,\qquad \int \partial_t\varphi\, f=-\int \varphi\, g_t$$
--
--   for every real $\varphi\in C^\infty_c(U)$, and $g_s,g_t\in L^p(K)$ for every compact $K\subseteq U$.
--
--   This is the local-to-global principle for first-order weak derivatives on planar domains: membership in $W^{1,p}_{\mathrm{loc}}$ is a local property.
--
--   **Formalization Note** Weak partial derivatives are `HasWeakPartialsOn`, tested against real $C^\infty$ functions with compact support in the given open set; $\partial_s$ is the derivative in the direction $1$ and $\partial_t$ in the direction $i$. $p$ is an `ENNReal`, and $L^p$ membership is `MemLp` for Lebesgue measure restricted to the set. Integrability of $f$ on compacts is needed because the weak-derivative identity is stated with Bochner integrals.
-- source:
--   Standard (weak derivatives and distribution theory).

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory
open scoped ContDiff

/-- Let `f` be integrable on every compact subset of an open set `U ⊆ ℂ`. If every point of `U`
has an open neighbourhood `V ⊆ U` on which `f` has weak partial derivatives lying in
`L^p(V)` (`1 ≤ p`), then `f` has weak partial derivatives on all of `U`, and these lie in
`L^p(K)` for every compact `K ⊆ U`. -/
theorem HasWeakPartialsOn.of_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {U : Set ℂ} (hU : IsOpen U) {p : ENNReal} (hp : 1 ≤ p) {f : ℂ → E}
    (hf : ∀ K ⊆ U, IsCompact K → IntegrableOn f K)
    (hloc : ∀ z ∈ U, ∃ V : Set ℂ, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧ ∃ gs gt : ℂ → E,
      HasWeakPartialsOn V f gs gt ∧ MemLp gs p (volume.restrict V) ∧
        MemLp gt p (volume.restrict V)) :
    ∃ gs gt : ℂ → E, HasWeakPartialsOn U f gs gt ∧
      ∀ K ⊆ U, IsCompact K → MemLp gs p (volume.restrict K) ∧ MemLp gt p (volume.restrict K) := by
  sorry

end JHolomorphic
