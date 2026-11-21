-- Prove2me | Theorems.Thm_MasulloGRH_finestLC_subspaces
-- name    : MasulloGRH.finestLC_subspaces
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:40:51.566621+00:00
-- url     : https://prove2.me/theorems/cc8f18b7-2829-4d77-85ec-5661362f1ce7
-- title:
--   Proposition C.2.5.1(3) — subspaces are closed and complemented; the finest topology passes to subspaces and quotients
-- statement:
--   Let $E$ be a complex vector space equipped with its finest locally convex topology $\tau$, and let $V\subseteq E$ be any linear subspace. Then:
--
--   1. $V$ is closed in $E$;
--   2. $V$ is topologically complemented: there is a continuous linear projection of $E$ onto $V$;
--   3. the topology induced by $\tau$ on $V$ is the finest locally convex topology of $V$;
--   4. the quotient topology on $E/V$ is the finest locally convex topology of $E/V$.
--
--   In the words of the source: every linear subspace is $\tau$-closed and topologically complemented, so $\tau$ is inherited by all linear subspaces and quotients.
--
--   The source's statement (3) also asserts that $(E,\tau)$ is complete; that assertion is **not** included here.
--
--   **Formalization Note.** "Topologically complemented" is Mathlib's `Submodule.ClosedComplemented`: the existence of a continuous linear map $E\to V$ restricting to the identity on $V$. The subspace and the quotient carry their instance topologies (induced and quotient topology), and "is the finest locally convex topology" is the mission predicate `HasFinestLocallyConvexTopology`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Proposition C.2.5.1(3), p. 691 (first sentence; the completeness assertion of (3) is not part of this statement).

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u v

theorem finestLC_subspaces (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (h : HasFinestLocallyConvexTopology E) (V : Submodule ℂ E) :
    IsClosed (V : Set E) ∧ V.ClosedComplemented ∧
      HasFinestLocallyConvexTopology V ∧ HasFinestLocallyConvexTopology (E ⧸ V) := by sorry

end MasulloGRH
