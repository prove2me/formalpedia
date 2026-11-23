-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_gs_appLE
-- name    : GlobalTheory.VeryAmplePow.gs_appLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:01.332924+00:00
-- url     : https://prove2.me/theorems/e8c7aa8f-da97-4bc7-83d1-29c855a30ec5
-- title:
--   Very Ample Pow: gs app LE
-- statement:
--   The Very Ample Pow construction uses the gs app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L128-L131

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
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
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem GlobalTheory.VeryAmplePow.gs_appLE {Z' Z Y : Scheme.{0}} (q : Z' ⟶ Z) (r : Z ⟶ Y) (z : Z') (U : Y.Opens) (V : Z.Opens)
    (hle : V ≤ r ⁻¹ᵁ U) (h : q z ∈ V) (a : Γ(Y, U)) :
    gs q z V ((r.appLE U V hle).hom a) = gs (q ≫ r) z U a := by sorry
