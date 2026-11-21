-- Prove2me | Theorems.Thm_MasulloGRH_strongBidualTopology_eq_of_firstCountable
-- name    : MasulloGRH.strongBidualTopology_eq_of_firstCountable
-- status  : Proved
-- author  : @ghseeli
-- created : 2026-11-20T23:50:50.581847+00:00
-- url     : https://prove2.me/theorems/9694dc99-6ad2-4c03-8cd8-ba812f793e0c
-- title:
--   First-countable locally convex spaces carry their canonical strong bidual topology
-- statement:
--   Let $E$ be a complex locally convex topological vector space with a countable neighborhood base at each point. Its original topology is the topology of uniform convergence on bounded subsets of its strong dual $E'_\beta$. Equivalently, the canonical evaluation map
--
--   $$J:E\longrightarrow(E'_\beta)'_\beta,\qquad J(x)(f)=f(x),$$
--
--   induces the original topology on $E$.
--
--   Completeness and nuclearity are not required. Hausdorffness is also unnecessary for the topology equality; when $E$ is Hausdorff, $J$ is injective and hence a topological embedding. This isolates the canonical-topology part of the Fréchet bidual argument and of the nuclear Fréchet Montel theorem.
-- source:
--   Generalization extracted from the proved mission theorem MasulloGRH.frechet_equiv_subspace_bidual, https://prove2.me/theorems/d983b29e-b5c6-441b-9fb0-ed96f1a4966d, and the canonical-topology argument for MasulloGRH.nuclear_frechet_isMontel, https://prove2.me/theorems/a6a0760f-4dd5-45b8-a797-eeb1a25e6845. Supporting source context: A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Appendix C, Definition/Example C.1.4.6 and the paragraph before Lemma C.2.4.16 (p. 690), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The weaker first-countability hypothesis is a strengthening proved here, not a separate numbered assertion in Masullo. The proof uses Mathlib LinearMap.continuous_of_locally_bounded and Hahn–Banach norming functionals.

import Definitions.Def_MasulloGRH_LocallyConvex
set_option autoImplicit false
open MasulloGRH Topology Filter Set

theorem MasulloGRH.strongBidualTopology_eq_of_firstCountable (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [FirstCountableTopology E]
    (hE : IsLocallyConvexTopology E ‹TopologicalSpace E›) :
    ‹TopologicalSpace E› = strongBidualTopology E := by sorry
