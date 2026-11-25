-- Prove2me | Theorems.Thm_GlobalTheory_TorsionTheta_tmul_one_ne_zero
-- name    : GlobalTheory.TorsionTheta.tmul_one_ne_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T14:59:24.843422+00:00
-- url     : https://prove2.me/theorems/7e00f156-c081-45d7-8051-729c45dabe5f
-- title:
--   Torsion Theta: tmul one ne zero
-- statement:
--   The Torsion Theta construction uses the tmul one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTorsionPointFrobeniusLocal.lean#L23-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniqueTorsionPointFrobeniusLocal.lean#L23-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueTorsionPointFrobeniusLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TorsionTheta

theorem GlobalTheory.TorsionTheta.tmul_one_ne_zero {O : Type} [CommRing O] [IsLocalRing O] {H : Type} [CommRing H]
    [Algebra O H] [Module.Finite O H] [Module.Free O H] (l : H)
    (hl : l ∉ (IsLocalRing.maximalIdeal O).map (algebraMap O H))
    (K : Type) [Field K] [Algebra O K] : l ⊗ₜ[O] (1 : K) ≠ 0 := by sorry
