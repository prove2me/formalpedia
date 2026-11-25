-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_basicOpen_fibres_preirreducible_smooth
-- name    : GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:43.881827+00:00
-- url     : https://prove2.me/theorems/5be1cd9c-c128-4026-a76f-d239666b841b
-- title:
--   T: exists basic Open fibres preirreducible smooth
-- statement:
--   The T construction uses the exists basic Open fibres preirreducible smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpenFibresPreirreducibleSmoothStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpenFibresPreirreducibleSmoothStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmoothStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_basicOpen_fibres_preirreducible_smooth : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B → ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) → PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) → ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧ (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → IsPreirreducible {r : PrimeSpectrum B | r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by sorry
