-- Prove2me | Theorems.Thm_GlobalTheory_T_splitTorus_to_abelianVariety_const
-- name    : GlobalTheory.T.splitTorus_to_abelianVariety_const
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:58:44.096994+00:00
-- url     : https://prove2.me/theorems/2fa039a5-2691-47ed-b032-17f4de5cb66b
-- title:
--   T: split Torus to abelian Variety const
-- statement:
--   The T construction uses the split Torus to abelian Variety const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConstStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConstStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConstStatement
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

theorem GlobalTheory.T.splitTorus_to_abelianVariety_const : ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus (Sp K) X ⟶ B, ∃ b : 𝟙_ (Over (Sp K)) ⟶ B, f = toUnit _ ≫ b := by sorry
