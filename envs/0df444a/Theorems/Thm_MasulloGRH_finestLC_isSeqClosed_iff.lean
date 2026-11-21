-- Prove2me | Theorems.Thm_MasulloGRH_finestLC_isSeqClosed_iff
-- name    : MasulloGRH.finestLC_isSeqClosed_iff
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:48:40.238774+00:00
-- url     : https://prove2.me/theorems/2e41d540-9eaa-4a82-823e-8b84d094e00c
-- title:
--   Proposition C.2.5.1(5) — sequentially closed sets for the finest locally convex topology
-- statement:
--   Let $E$ be a complex vector space equipped with its finest locally convex topology $\tau$. A subset $C\subseteq E$ is $\tau$-sequentially closed if and only if
--
--   $$C\cap V\ \text{is closed for every finite-dimensional linear subspace } V\subseteq E .$$
--
--   Sequentially closed means that the limit of every $\tau$-convergent sequence of points of $C$ lies in $C$.
--
--   The criterion reduces sequential questions for $\tau$ to finite-dimensional ones; it rests on the fact that convergent sequences are bounded and bounded sets are finite-dimensional (part (4) of the same proposition).
--
--   **Formalization Note.** `IsSeqClosed` is Mathlib's notion of sequential closedness. The set $C\cap V$ is regarded as a subset of $E$; since every finite-dimensional subspace is closed in $E$, being closed in $E$ is the same as being closed in $V$ for its Euclidean topology.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Proposition C.2.5.1(5), p. 692.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u

theorem finestLC_isSeqClosed_iff (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) (C : Set E) :
    IsSeqClosed C ↔
      ∀ V : Submodule ℂ E, FiniteDimensional ℂ V → IsClosed (C ∩ (V : Set E)) := by sorry

end MasulloGRH
