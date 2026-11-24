-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_Seesaw_exists_minor
-- name    : GlobalTheory.AbLaw.Seesaw.exists_minor
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:51:44.396895+00:00
-- url     : https://prove2.me/theorems/8f5591fa-cab1-4e63-be7b-4fba5046c0f3
-- title:
--   Seesaw: exists minor
-- statement:
--   The Seesaw construction uses the exists minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean#L14-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsKernelVector.lean#L14-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsKernelVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw

theorem GlobalTheory.AbLaw.Seesaw.exists_minor {K m n : Type} [Field K] [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n K)
    (hA : ∀ w, A.mulVec w = 0 → w = 0) : ∃ ρ : n → m, (A.submatrix ρ id).det ≠ 0 := by sorry
