-- Prove2me | Theorems.Thm_GlobalTheory_NatFun_pull_comp
-- name    : GlobalTheory.NatFun.pull_comp
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:40.457128+00:00
-- url     : https://prove2.me/theorems/7e46711d-3fb0-4ab1-ab74-061b1397268c
-- title:
--   Nat Fun: pull comp
-- statement:
--   The Nat Fun construction uses the pull comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasChartsOfForallIsAffineOpen.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasChartsOfForallIsAffineOpen.lean#L37-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_left

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
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap spMap_left spMap_comp)
open GlobalTheory GlobalTheory.NatFun
variable {k : Type} [CommRing k]

theorem GlobalTheory.NatFun.pull_comp {X Y Z : Over (Spec (CommRingCat.of k))} (m : Z ⟶ Y) (n : Y ⟶ X)
    (s : Γ(X.left, ⊤)) : pull (m ≫ n) s = pull m (pull n s) := by sorry
