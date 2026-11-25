-- Prove2me | Theorems.Thm_GlobalTheory_T_geomRegFib_of_isRegularRing_tensor_essFiniteType
-- name    : GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:33:33.670475+00:00
-- url     : https://prove2.me/theorems/87ad61fd-2b0b-4c66-be13-eadc5ead04bc
-- title:
--   T: geom Reg Fib of is Regular Ring tensor ess Finite Type
-- statement:
--   The T construction uses the geom Reg Fib of is Regular Ring tensor ess Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeomRegFibOfIsRegularRingTensorEssFiniteTypeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GeomRegFibOfIsRegularRingTensorEssFiniteTypeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeomRegFibOfIsRegularRingTensorEssFiniteType
import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinTypeQE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GeomRegFibOfIsRegularRingTensorEssFiniteTypeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) → FinalTheorems.GeomRegFib R B := by sorry
