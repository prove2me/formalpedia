-- Prove2me | Theorems.Thm_JHolomorphic_eventuallyEq_of_iteratedFDeriv_eq
-- name    : JHolomorphic.eventuallyEq_of_iteratedFDeriv_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-20T20:33:13.815328+00:00
-- url     : https://prove2.me/theorems/a24a0cfa-bedb-4bde-90db-f9c54b7656e9
-- title:
--   Unique continuation for pseudoholomorphic maps
-- statement:
--   Let $E$ be a finite-dimensional real vector space, let $J$ be a smooth almost complex structure on an open set $O\subseteq E$, and let $D\subset\mathbb{C}$ be the open unit disc. If $u,v:D\to O$ are $C^\infty$ and $J$-holomorphic, and all their derivatives of all orders (including order $0$) agree at $0$, then $u=v$ on a neighbourhood of $0$.
--
--   **Formalization Note** The hypotheses are `ContDiffOn ℝ ∞`, `IsJHolomorphicOn J (ball 0 1)` and `Set.MapsTo _ (ball 0 1) O` for $u$ and $v$, and `∀ m, iteratedFDeriv ℝ m u 0 = iteratedFDeriv ℝ m v 0`. Wendl takes $E=O=\mathbb{C}^n$ and $u(0)=v(0)=0$. The conclusion is `u =ᶠ[𝓝 0] v`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Proposition 2.28, p. 40

import Definitions.Def_JHolomorphic_Setting

namespace JHolomorphic

open MeasureTheory Metric Filter Topology DbarRegularity
open scoped ContDiff ENNReal NNReal

/-- Wendl, Proposition 2.28 (p. 40): let `J` be a smooth almost complex structure on an open set
`O ⊆ E`. Two smooth `J`-holomorphic maps `u`, `v` on the open unit disc with values in `O` whose
derivatives of all orders (including order `0`) agree at `0` coincide on a neighbourhood
of `0`. -/
theorem eventuallyEq_of_iteratedFDeriv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (u v : ℂ → E)
    (hu : ContDiffOn ℝ ∞ u (ball 0 1)) (hv : ContDiffOn ℝ ∞ v (ball 0 1))
    (huh : IsJHolomorphicOn J (ball 0 1) u) (hvh : IsJHolomorphicOn J (ball 0 1) v)
    (hum : Set.MapsTo u (ball 0 1) O) (hvm : Set.MapsTo v (ball 0 1) O)
    (hD : ∀ m : ℕ, iteratedFDeriv ℝ m u 0 = iteratedFDeriv ℝ m v 0) :
    u =ᶠ[𝓝 0] v := by
  sorry

end JHolomorphic
