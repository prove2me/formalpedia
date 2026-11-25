-- Prove2me | Theorems.Thm_GlobalTheory_exists_basicOpen_fibres_preirreducible
-- name    : GlobalTheory.exists_basicOpen_fibres_preirreducible
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:31:33.380696+00:00
-- url     : https://prove2.me/theorems/d8bd7b02-4687-4578-bfca-5a36178bd1ef
-- title:
--   Global Theory: exists basic Open fibres preirreducible
-- statement:
--   The Global Theory construction uses the exists basic Open fibres preirreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpenFibresPreirreducibleSmooth.lean#L10-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpenFibresPreirreducibleSmooth.lean#L10-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleFibreStandardEtaleSpreadsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RangeComapIncludeRightFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleTensorLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenFibresPreirreducibleSmooth
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
open GlobalTheory

theorem GlobalTheory.exists_basicOpen_fibres_preirreducible :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B], Algebra.Smooth A B →
    ∀ (q : PrimeSpectrum B) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω],
    q.asIdeal.comap (algebraMap A B) = RingHom.ker (algebraMap A Ω) →
    PreirreducibleSpace (PrimeSpectrum (Ω ⊗[A] B)) →
    ∃ (b : B) (a : A) (I : Finset A), b ∉ q.asIdeal ∧ algebraMap A B a ∉ q.asIdeal ∧
      (∀ c ∈ I, algebraMap A B c ∈ q.asIdeal) ∧
      ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) →
        IsPreirreducible {r : PrimeSpectrum B |
          r.asIdeal.comap (algebraMap A B) = t.asIdeal ∧ b ∉ r.asIdeal} := by sorry
