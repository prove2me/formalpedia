-- Prove2me | Theorems.Thm_MasulloGRH_hilbert_quotient_biorthogonal_section
-- name    : MasulloGRH.hilbert_quotient_biorthogonal_section
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:50:15.375083+00:00
-- url     : https://prove2.me/theorems/792622fb-0a65-4ca8-a393-f26f7b54bc12
-- title:
--   Simultaneous Hilbert quotient lifts arbitrarily close to the orthogonal section
-- statement:
--   Let K be a closed subspace of a real or complex Hilbert space E. Let F be a linear subspace such that K ∩ F is dense in K. Suppose each member x_n of a countable continuous biorthogonal system in E/K has some lift in F. Write J for the canonical isometric section with image K orthogonal. For every ε>0 there exists a continuous linear section T of the quotient map with ‖T−J‖<ε and T(x_n)∈F for all n.
--
--   The quotient map is a left inverse, so T transports the system isomorphically onto its image. In particular a Schauder sequence remains Schauder there, and a Markushevich system retains its own expansion properties. No uniform bound on the biorthogonal functionals is necessary. This supplies Hilbert-space lifts of the type required for (10.4.2.23)–(10.4.2.24), conditional on membership of the quotient vectors in the image of the test subspace.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Lemma 10.4.2.5, pp. 461–462; Remarks 10.4.2.6–7; the proof of Theorem 10.4.2.8 invokes the lemma on p. 464. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecificLimits.Normed

open Set Filter Topology
open scoped InnerProductSpace

theorem MasulloGRH.hilbert_quotient_biorthogonal_section {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (K F : Submodule 𝕜 E) [IsClosed (K : Set E)]
    (hd : K ≤ (K ⊓ F).topologicalClosure) (x : ℕ → E ⧸ K) (f : ℕ → StrongDual 𝕜 (E ⧸ K))
    (hbi : ∀ n m, f n (x m) = if n=m then 1 else 0)
    (hx : ∀ n, ∃ y ∈ F, K.mkQ y = x n) (ε : ℝ) (hε : 0 < ε) :
    let J : (E ⧸ K) →L[𝕜] E := Kᗮ.subtypeL.comp K.quotientEquivOrthogonal.toLinearIsometry.toContinuousLinearMap
    ∃ T : (E ⧸ K) →L[𝕜] E, (∀ y, K.mkQ (T y) = y) ∧ (∀ n, T (x n) ∈ F) ∧ ‖T-J‖ < ε := by sorry
