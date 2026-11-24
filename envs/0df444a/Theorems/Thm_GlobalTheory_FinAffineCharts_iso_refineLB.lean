-- Prove2me | Theorems.Thm_GlobalTheory_FinAffineCharts_iso_refineLB
-- name    : GlobalTheory.FinAffineCharts.iso_refineLB
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:24:52.367129+00:00
-- url     : https://prove2.me/theorems/2e829fe2-6cb8-436e-8885-2b45f108ac51
-- title:
--   Fin Affine Charts: iso refine LB
-- statement:
--   The Fin Affine Charts construction uses the iso refine LB property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteAffineCharts.lean#L46-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFiniteAffineCharts.lean#L46-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFiniteAffineCharts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.FinAffineCharts
variable {X : Scheme.{0}}

theorem GlobalTheory.FinAffineCharts.iso_refineLB {L : LB X} (hL : L.IsLB) {κ : Type} (W : κ → X.Opens) (c : κ → L.ι)
    (h : ∀ a, W a ≤ L.U (c a)) : LBIso L (refineLB L W c h) := by sorry
