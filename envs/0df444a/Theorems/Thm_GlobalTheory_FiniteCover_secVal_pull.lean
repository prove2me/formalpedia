-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCover_secVal_pull
-- name    : GlobalTheory.FiniteCover.secVal_pull
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:27:07.144632+00:00
-- url     : https://prove2.me/theorems/ba6bdd6e-77ed-438f-b7e9-567ddac403bb
-- title:
--   Finite Cover: sec Val pull
-- statement:
--   The Finite Cover construction uses the sec Val pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean#L129-L133

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

theorem GlobalTheory.FiniteCover.secVal_pull (φ : X' ⟶ X) [IsDominant φ] {V : X.Opens} (hV : genericPoint X ∈ V)
    (h₀' : genericPoint X' ∈ (M.pull φ).U fun _ => k₀) (hV' : genericPoint X' ∈ φ ⁻¹ᵁ V)
    (σ : SecOn M V) :
    secVal h₀' hV' (SecOn.pull M φ V σ) = functionFieldMap φ (secVal h₀ hV σ) := by sorry
