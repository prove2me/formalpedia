-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCover_toField_coord
-- name    : GlobalTheory.FiniteCover.toField_coord
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:32.905278+00:00
-- url     : https://prove2.me/theorems/5c513f3c-d43e-47b0-bc52-9579d555e43e
-- title:
--   Finite Cover: to Field coord
-- statement:
--   The Finite Cover construction uses the to Field coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean#L57-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecValEqIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.FiniteCover
variable {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
variable {M : LB X} {k₀ : M.ι} (h₀ : genericPoint X ∈ M.U k₀)

theorem GlobalTheory.FiniteCover.toField_coord {V : X.Opens} (hV : genericPoint X ∈ V) (σ : SecOn M V) {k : M.ι}
    (hk : genericPoint X ∈ M.U k) :
    toField (U := V ⊓ M.U k) (generic_inf (hV) (hk)) (GlobalTheory.LB.coord σ k) =
      toField (U := M.U k ⊓ M.U k₀) (generic_inf (hk) (h₀)) (M.g k k₀).val * secVal h₀ hV σ := by sorry
