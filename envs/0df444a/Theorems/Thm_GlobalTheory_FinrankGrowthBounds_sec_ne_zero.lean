-- Prove2me | Theorems.Thm_GlobalTheory_FinrankGrowthBounds_sec_ne_zero
-- name    : GlobalTheory.FinrankGrowthBounds.sec_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:31:06.572452+00:00
-- url     : https://prove2.me/theorems/008db574-21de-49a2-bc13-c1fae55ee320
-- title:
--   Finrank Growth Bounds: sec ne zero
-- statement:
--   The Finrank Growth Bounds construction uses the sec ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L154-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FinrankSectionsLineBundlePowEqPow.lean#L154-L173

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

theorem GlobalTheory.FinrankGrowthBounds.sec_ne_zero {X : Scheme.{0}} [IsIntegral X] {M : LB X} (s : LB.Sec M) {i₀ : M.ι}
    (h₀ : s.f i₀ ≠ 0) (i : M.ι) [hi : Nonempty (M.U i)] : s.f i ≠ 0 := by sorry
