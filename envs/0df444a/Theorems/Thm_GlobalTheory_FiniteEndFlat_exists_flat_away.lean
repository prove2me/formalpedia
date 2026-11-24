-- Prove2me | Theorems.Thm_GlobalTheory_FiniteEndFlat_exists_flat_away
-- name    : GlobalTheory.FiniteEndFlat.exists_flat_away
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:34.540363+00:00
-- url     : https://prove2.me/theorems/a846733c-83b0-4778-bc89-b4f5e52ea801
-- title:
--   Finite End Flat: exists flat away
-- statement:
--   The Finite End Flat construction uses the exists flat away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatAndSurjectiveOfIsFiniteAbelianEnd.lean#L47-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatAndSurjectiveOfIsFiniteAbelianEnd.lean#L47-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FiniteEndFlat

theorem GlobalTheory.FiniteEndFlat.exists_flat_away {A B : Type} [CommRing A] [CommRing B] [IsDomain A] [IsNoetherianRing A]
    (φ : A →+* B) (hφ : φ.Finite) :
    ∃ r : A, r ≠ 0 ∧ ∀ (C : Type) [CommRing C] [Algebra B C] [IsLocalization.Away (φ r) C],
      ((algebraMap B C).comp φ).Flat := by sorry
