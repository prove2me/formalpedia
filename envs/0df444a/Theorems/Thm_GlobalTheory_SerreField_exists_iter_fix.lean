-- Prove2me | Theorems.Thm_GlobalTheory_SerreField_exists_iter_fix
-- name    : GlobalTheory.SerreField.exists_iter_fix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:42.049931+00:00
-- url     : https://prove2.me/theorems/ec53fb07-7aba-49d3-8221-b777789857c6
-- title:
--   Serre Field: exists iter fix
-- statement:
--   The Serre Field construction uses the exists iter fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsOddNeZero.lean#L94-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsOddNeZero.lean#L94-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulPullOfCubeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsOddNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SerreField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.MulPull
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
variable {A}

theorem GlobalTheory.SerreField.exists_iter_fix (σ : A ≅ A) [IsMonHom σ.hom] (T : Over S) (n : ℕ)
    [Finite {x : T ⟶ A // x ^ n = 1}] :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ x : T ⟶ A, x ^ n = 1 → x ≫ (iter σ m).hom = x := by sorry
