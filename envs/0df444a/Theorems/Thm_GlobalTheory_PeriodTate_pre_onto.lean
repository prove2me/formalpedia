-- Prove2me | Theorems.Thm_GlobalTheory_PeriodTate_pre_onto
-- name    : GlobalTheory.PeriodTate.pre_onto
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:41:41.796438+00:00
-- url     : https://prove2.me/theorems/72844238-08d8-432a-85dd-fc3faacdf071
-- title:
--   Period Tate: pre onto
-- statement:
--   The Period Tate construction uses the pre onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsTateIsoOfPeriods.lean#L85-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsTateIsoOfPeriods.lean#L85-L103

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsTateIsoOfPeriods
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PeriodTate

theorem GlobalTheory.PeriodTate.pre_onto (hM : Out.MulNSt) {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (Q : Out.PolAV (Sp ℂ))
    {n : ℕ} (hn : 0 < n) (x : Over.mk (spMap β) ⟶ Q.A) (hx : x ^ n = 1) :
    ∃ y : 𝟙_ (Over (Sp ℂ)) ⟶ Q.A, y ^ n = 1 ∧ toUnit _ ≫ y = x := by sorry
