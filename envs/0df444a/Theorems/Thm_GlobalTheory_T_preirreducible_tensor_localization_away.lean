-- Prove2me | Theorems.Thm_GlobalTheory_T_preirreducible_tensor_localization_away
-- name    : GlobalTheory.T.preirreducible_tensor_localization_away
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:51.053535+00:00
-- url     : https://prove2.me/theorems/ed2f1355-7b61-498f-824d-9c0160a45f96
-- title:
--   T: preirreducible tensor localization away
-- statement:
--   The T construction uses the preirreducible tensor localization away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleTensorLocalizationAwayStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreirreducibleTensorLocalizationAwayStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleTensorLocalizationAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreirreducibleTensorLocalizationAwayStatement
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

theorem GlobalTheory.T.preirreducible_tensor_localization_away : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by sorry
