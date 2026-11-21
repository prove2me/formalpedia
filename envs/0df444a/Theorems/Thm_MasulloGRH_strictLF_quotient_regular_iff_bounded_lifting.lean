-- Prove2me | Theorems.Thm_MasulloGRH_strictLF_quotient_regular_iff_bounded_lifting
-- name    : MasulloGRH.strictLF_quotient_regular_iff_bounded_lifting
-- status  : Proved
-- author  : @Abhishek Anand
-- created : 2026-11-20T23:43:13.581532+00:00
-- url     : https://prove2.me/theorems/f23cf614-9df5-400f-9b3b-44d0acefeaca
-- title:
--   Bounded lifting is equivalent to regularity of the quotient stages
-- statement:
--   For a strict countable inductive limit of nuclear Fréchet spaces and a closed subspace, bounded lifting to the ambient space is equivalent to covering each bounded set in the quotient by the image of a bounded set in one stage quotient. This is the bounded-set step in the proof of Wengenroth’s Corollary 3.4 cited by Masullo.
-- source:
--   Masullo, The Music of the Primes, Theorem C.1.5.11, p. 668, citing J. Wengenroth, Acyclic inductive spectra of Fréchet spaces, Studia Math. 120 (1996), Corollary 3.4, p. 254. https://doi.org/10.4064/sm-120-3-247-258

import Definitions.Def_MasulloGRH_LocallyConvex
open MasulloGRH

theorem MasulloGRH.strictLF_quotient_regular_iff_bounded_lifting (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) :
    LiftsBoundedSets (V.mkQ : E → E ⧸ V) ↔
    ∀ B : Set (E ⧸ V), Bornology.IsVonNBounded ℂ B →
      ∃ (n : ℕ) (A : Set (X n ⧸ V.comap (X n).subtype)), Bornology.IsVonNBounded ℂ A ∧
        B ⊆ Submodule.mapQ (V.comap (X n).subtype) V (X n).subtype le_rfl '' A := by sorry
