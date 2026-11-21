-- Prove2me | Theorems.Thm_MasulloGRH_nuclearFrechet_quotient_bounded_compact_closure
-- name    : MasulloGRH.nuclearFrechet_quotient_bounded_compact_closure
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:53:40.941438+00:00
-- url     : https://prove2.me/theorems/43b9d65e-f390-40c2-90e5-f88b014e1c12
-- title:
--   Bounded subsets of a nuclear Fréchet stage quotient have compact closure
-- statement:
--   For a closed subspace of a nuclear Fréchet space, the closure of each bounded subset in the quotient is compact. This is the compactness of the stage quotients used in Wengenroth’s Corollary 3.4. The lift and precompactness estimates are supplied by previously verified results.
-- source:
--   Masullo, The Music of the Primes, Theorem C.1.5.11, p. 668, citing J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), Corollary 3.4, p. 254. https://doi.org/10.4064/sm-120-3-247-258

import Definitions.Def_MasulloGRH_LocallyConvex
open MasulloGRH

theorem MasulloGRH.nuclearFrechet_quotient_bounded_compact_closure (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hF : IsFrechet E) (hN : IsNuclear E) (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (B : Set (E ⧸ V)) (hB : Bornology.IsVonNBounded ℂ B) : IsCompact (closure B) := by sorry
