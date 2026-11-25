-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCover_toField_appLE
-- name    : GlobalTheory.FiniteCover.toField_appLE
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:46.87581+00:00
-- url     : https://prove2.me/theorems/f4a1d232-d692-4f5d-b2a2-e10d795deb94
-- title:
--   Finite Cover: to Field app LE
-- statement:
--   The Finite Cover construction uses the to Field app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean#L43-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean#L43-L50

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

theorem GlobalTheory.FiniteCover.toField_appLE (φ : X' ⟶ X) [IsDominant φ] {U : X.Opens} {V : X'.Opens} (e : V ≤ φ ⁻¹ᵁ U)
    (hU : genericPoint X ∈ U) (hV : genericPoint X' ∈ V) (a : Γ(X, U)) :
    toField hV ((φ.appLE U V e).hom a) = functionFieldMap φ (toField hU a) := by sorry
