-- Prove2me | Theorems.Thm_MasulloGRH_finestLC_linearMap_continuous
-- name    : MasulloGRH.finestLC_linearMap_continuous
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:40:50.321179+00:00
-- url     : https://prove2.me/theorems/2bc1ad01-da22-4924-9846-31444f2baabe
-- title:
--   Proposition C.2.5.1(2) — every linear map out of the finest locally convex topology is continuous
-- statement:
--   Let $E$ be a complex vector space equipped with its finest locally convex topology $\tau$.
--
--   1. For every Hausdorff locally convex topological vector space $M$, every linear map
--
--   $$T\colon E\longrightarrow M$$
--
--   is continuous.
--
--   2. In particular every linear functional on $E$ is continuous, so the topological dual $(E,\tau)'$ equals the algebraic dual $E^{*}$.
--
--   This automatic-continuity property is what makes the finest locally convex topology convenient for spaces of locally constant compactly supported functions: no continuity verification is ever needed for linear maps defined on them.
--
--   **Formalization Note.** $M$ ranges over an arbitrary universe; Hausdorff local convexity is the mission predicate `IsHLCS`. The second assertion is stated as continuity of every `E →ₗ[ℂ] ℂ`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Proposition C.2.5.1(2), p. 691.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u v

theorem finestLC_linearMap_continuous (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) :
    (∀ (M : Type v) [AddCommGroup M] [Module ℂ M] [TopologicalSpace M], IsHLCS M →
      ∀ T : E →ₗ[ℂ] M, Continuous T) ∧
    ∀ f : E →ₗ[ℂ] ℂ, Continuous f := by sorry

end MasulloGRH
