-- Prove2me | Theorems.Thm_GlobalTheory_preirreducibleSpace_primeSpectrum_tensor_localizationAway
-- name    : GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:15:12.535147+00:00
-- url     : https://prove2.me/theorems/b45da1a9-b23d-4d03-b989-be3f4188bdc6
-- title:
--   Global Theory: preirreducible Space prime Spectrum tensor localization Away
-- statement:
--   The Global Theory construction uses the preirreducible Space prime Spectrum tensor localization Away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleTensorLocalizationAway.lean#L8-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleTensorLocalizationAway.lean#L8-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleTensorLocalizationAway
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

theorem GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway
    (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k]
    [Algebra A k] :
    PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) →
      PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by sorry
