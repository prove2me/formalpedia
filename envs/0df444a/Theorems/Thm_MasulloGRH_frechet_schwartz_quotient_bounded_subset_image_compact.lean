-- Prove2me | Theorems.Thm_MasulloGRH_frechet_schwartz_quotient_bounded_subset_image_compact
-- name    : MasulloGRH.frechet_schwartz_quotient_bounded_subset_image_compact
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T09:22:22.566817+00:00
-- url     : https://prove2.me/theorems/3a7b4226-db1e-4f9d-bf27-1139cac21e53
-- title:
--   Grothendieck: every bounded subset of a quotient of a Fréchet–Schwartz space is contained in the image of a compact set
-- statement:
--   **Lifting of bounded sets through quotients of Fréchet–Schwartz spaces (Grothendieck).** Let $E$ be a Fréchet space over $\mathbb C$ which is a Schwartz space in the sense of Grothendieck, let $F\subset E$ be a closed linear subspace, and let
--   $$q\colon E\to E/F$$
--   be the quotient map, $E/F$ carrying the quotient topology. Then for every bounded subset $B\subset E/F$ there is a compact subset $C\subset E$ with
--   $$B\subset q(C).$$
--
--   In particular $q$ has the *bounded lifting property* of Definition C.1.5.9 of the source (every bounded subset of $E/F$ is contained in the image of a bounded subset of $E$), and, taking $F=0$, every bounded subset of a Fréchet–Schwartz space is relatively compact.
--
--   This is the result the source quotes as the origin of the bounded lifting property: applied to nuclear Fréchet spaces, which are Schwartz spaces, it gives the lifting of bounded sets through the quotients $E_m\to E_m/(F\cap E_m)$ in the proof of Corollary C.1.5.13.
--
--   **Formalization Note.** `MasulloGRH.IsFrechet` (locally convex, complete, metrizable) and the new predicate `MasulloGRH.IsSchwartzLCS` are properties of the topology of `E`. The subspace is a `Submodule ℂ E` whose carrier is closed, `E ⧸ W` carries Mathlib's quotient topology, bounded means von Neumann bounded, and $q$ is `W.mkQ`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 667, §C.1.5, paragraph after Definition C.1.5.9; classical reference: A. Grothendieck, Sur les espaces (F) et (DF), Summa Brasil. Math. 3 (1954), pp. 57-123, II.4, Théorème 12, p. 119 (as cited by the paper)

import Mathlib
import Definitions.Def_MasulloGRH_LocallyConvex
import Definitions.Def_LocallyConvex_SchwartzSpace

open Topology

set_option autoImplicit false

namespace MasulloGRH

theorem frechet_schwartz_quotient_bounded_subset_image_compact (E : Type*) [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] (hF : IsFrechet E) (hS : IsSchwartzLCS E)
    (W : Submodule ℂ E) (hW : IsClosed (W : Set E)) (B : Set (E ⧸ W))
    (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ C : Set E, IsCompact C ∧ B ⊆ W.mkQ '' C := by sorry

end MasulloGRH
