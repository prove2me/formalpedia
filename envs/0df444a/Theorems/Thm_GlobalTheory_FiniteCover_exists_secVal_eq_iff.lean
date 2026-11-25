-- Prove2me | Theorems.Thm_GlobalTheory_FiniteCover_exists_secVal_eq_iff
-- name    : GlobalTheory.FiniteCover.exists_secVal_eq_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:35:21.136825+00:00
-- url     : https://prove2.me/theorems/92238ba8-9899-5792-83ee-ff067b2b6e90
-- title:
--   Finite Cover: exists sec Val eq iff
-- statement:
--   The Finite Cover construction uses the exists sec Val eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean#L89-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecValEqIff.lean#L89-L119

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

theorem GlobalTheory.FiniteCover.exists_secVal_eq_iff (hM : M.IsLB) {I : Type} (D : I → X.Opens) (hc : ⊤ ≤ ⨆ i, D i)
    (hη : ∀ i, genericPoint X ∈ D i) (τ : ∀ i, SecOn M (D i))
    (hτ : ∀ i k, IsUnit (GlobalTheory.LB.coord (τ i) k)) (x : X.functionField) :
    (∃ σ : SecOn M ⊤, secVal h₀ generic_top σ = x) ↔
      ∀ i, ∃ a ∈ (toField (hη i)).range, x = a * secVal h₀ (hη i) (τ i) := by sorry
