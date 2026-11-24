-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_generic_functionField_point
-- name    : GlobalTheory.T.exists_generic_functionField_point
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:36:43.074192+00:00
-- url     : https://prove2.me/theorems/d659a7a7-8005-429b-ac2c-9b352b786719
-- title:
--   T: exists generic function Field point
-- statement:
--   The T construction uses the exists generic function Field point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGenericFunctionFieldPointStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsGenericFunctionFieldPointStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPoint
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsUnitEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsGenericFunctionFieldPointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_generic_functionField_point : ∀ (Y : Scheme.{0}) [IsIntegral Y], ∃ (F : Type) (_ : Field F) (g : Sp F ⟶ Y) (hg : ∀ V : Y.Opens, (V : Set Y).Nonempty → ⊤ ≤ g ⁻¹ᵁ V), (∀ (V : Y.Opens) (hV : (V : Set Y).Nonempty), Function.Injective (WtRat.ev g V (hg V hV))) ∧ (∀ τ : Y ≅ Y, ∃ σ : F →+* F, spMap σ ≫ g = g ≫ τ.hom) ∧ ∀ U : Y.Opens, (U : Set Y).Nonempty → ∀ (I : Type) [Fintype I] (x : I → F), ∃ (U' : Y.Opens) (hU' : (U' : Set Y).Nonempty) (s : I → Γ(Y, U')), U' ≤ U ∧ ∀ j, WtRat.ev g U' (hg U' hU') (s j) = x j ∧ (x j ≠ 0 → IsUnit (s j)) := by sorry
