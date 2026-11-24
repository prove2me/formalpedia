-- Prove2me | Theorems.Thm_GlobalTheory_FinrankGrowthBounds_mulSec_injective
-- name    : GlobalTheory.FinrankGrowthBounds.mulSec_injective
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:31:07.224918+00:00
-- url     : https://prove2.me/theorems/37a524a8-fbb5-46d6-969e-097f42c4094e
-- title:
--   Finrank Growth Bounds: mul Sec injective
-- statement:
--   The Finrank Growth Bounds construction uses the mul Sec injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L203-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L203-L221

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FinrankSectionsLineBundlePowEqPow
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
set_option autoImplicit false
open GlobalTheory GlobalTheory.FinrankGrowthBounds
open Filter Topology
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S)

theorem GlobalTheory.FinrankGrowthBounds.mulSec_injective [IsIntegral (T ⊗ A).left] (a b : ℤ) (s : SecM A L b T) (hs : s ≠ 0) :
    Function.Injective (mulSec A L T a b s) := by sorry
