-- Prove2me | Theorems.Thm_GlobalTheory_T_isMonHom_pointed_splitExt_to_abelianVariety
-- name    : GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T14:48:31.498737+00:00
-- url     : https://prove2.me/theorems/e54c126d-20e4-4634-9fb7-6238640f256d
-- title:
--   T: is Mon Hom pointed split Ext to abelian Variety
-- statement:
--   The T construction uses the is Mon Hom pointed split Ext to abelian Variety property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsMonHomPointedSplitExtToAbelianVarietyStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsMonHomPointedSplitExtToAbelianVarietyStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsMonHomPointedSplitExtToAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsMonHomPointedSplitExtToAbelianVarietyStatement
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

theorem GlobalTheory.T.isMonHom_pointed_splitExt_to_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (E : SplitExt (Sp K)) (G : Over (Sp K)) [GrpObj G], E.IsGt G → ∀ (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : G ⟶ B, η[G] ≫ f = η[B] → IsMonHom f := by sorry
