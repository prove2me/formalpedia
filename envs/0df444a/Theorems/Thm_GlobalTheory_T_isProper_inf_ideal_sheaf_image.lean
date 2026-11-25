-- Prove2me | Theorems.Thm_GlobalTheory_T_isProper_inf_ideal_sheaf_image
-- name    : GlobalTheory.T.isProper_inf_ideal_sheaf_image
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:35.021545+00:00
-- url     : https://prove2.me/theorems/680ddad9-8583-4c13-b2a0-25115e593f6c
-- title:
--   T: is Proper inf ideal sheaf image
-- statement:
--   The T construction uses the is Proper inf ideal sheaf image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperInfIdealSheafImageStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsProperInfIdealSheafImageStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperInfIdealSheafImage
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BaseIdealIdeal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsProperInfIdealSheafImageStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isProper_inf_ideal_sheaf_image : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W), IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) → IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by sorry
