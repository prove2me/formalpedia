-- Prove2me | Theorems.Thm_MasulloGRH_finestLC_isVonNBounded_iff
-- name    : MasulloGRH.finestLC_isVonNBounded_iff
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:40:47.036394+00:00
-- url     : https://prove2.me/theorems/120f21c2-5301-439d-ae57-0cdb603511a3
-- title:
--   Proposition C.2.5.1(4) — bounded sets for the finest locally convex topology are finite-dimensional
-- statement:
--   Let $E$ be a complex vector space equipped with its finest locally convex topology $\tau$. A subset $B\subseteq E$ is bounded for $\tau$ if and only if
--
--   $$B\ \text{is contained in a finite-dimensional subspace } V\subseteq E\ \text{and is bounded for the Euclidean topology of } V .$$
--
--   Here bounded means von Neumann bounded: absorbed by every neighbourhood of $0$.
--
--   This is the description of bounded sets used in the source to treat $(E,\tau)$ as a locally convex direct sum of lines, and it underlies the later statements on sequential closedness and on the Montel property in the countable-dimensional case.
--
--   **Formalization Note.** The right-hand side asks for a finite-dimensional submodule $V$ and a von Neumann bounded subset $B'$ of $V$ (for the topology induced from $E$, which is the Euclidean topology because it is a Hausdorff vector space topology on a finite-dimensional space) whose image in $E$ is exactly $B$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Proposition C.2.5.1(4), p. 692.

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

namespace MasulloGRH

universe u v

theorem finestLC_isVonNBounded_iff (E : Type u) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (h : HasFinestLocallyConvexTopology E) (B : Set E) :
    Bornology.IsVonNBounded ℂ B ↔ ∃ V : Submodule ℂ E, FiniteDimensional ℂ V ∧
      ∃ B' : Set V, Bornology.IsVonNBounded ℂ B' ∧ B = Subtype.val '' B' := by sorry

end MasulloGRH
