-- Prove2me | Theorems.Thm_GlobalTheory_PullHermitian_unitVal_iso
-- name    : GlobalTheory.PullHermitian.unitVal_iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:48.27239+00:00
-- url     : https://prove2.me/theorems/688e1338-c40f-4d06-bddc-d201cd587b0d
-- title:
--   Pull Hermitian: unit Val iso
-- statement:
--   The Pull Hermitian construction uses the unit Val iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L73-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/HermFormPullEqOfLbIsoPow.lean#L73-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HermFormPullEqOfLbIsoPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.PullHermitian
variable {X : Scheme.{0}} (x : Sp ℂ ⟶ X)

theorem GlobalTheory.PullHermitian.unitVal_iso {M N : LB X} (w : LB.Iso N M) (hw : w.IsGen) (i i' : M.ι) (j j' : N.ι)
    (hi : ⊤ ≤ x ⁻¹ᵁ M.U i) (hi' : ⊤ ≤ x ⁻¹ᵁ M.U i') (hj : ⊤ ≤ x ⁻¹ᵁ N.U j)
    (hj' : ⊤ ≤ x ⁻¹ᵁ N.U j') :
    unitVal x (U := (LB.div M N).U (i, j)) (inf_of x hi hj) (w.s (i, j)) =
      unitVal x (inf_of x hi hi') (M.g i i') * (unitVal x (inf_of x hj hj') (N.g j j'))⁻¹ *
        unitVal x (U := (LB.div M N).U (i', j')) (inf_of x hi' hj') (w.s (i', j')) := by sorry
