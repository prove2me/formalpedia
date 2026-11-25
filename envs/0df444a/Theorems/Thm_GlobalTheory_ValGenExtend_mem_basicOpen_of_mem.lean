-- Prove2me | Theorems.Thm_GlobalTheory_ValGenExtend_mem_basicOpen_of_mem
-- name    : GlobalTheory.ValGenExtend.mem_basicOpen_of_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:23:36.104257+00:00
-- url     : https://prove2.me/theorems/03602b59-f92e-4251-b9b3-68376d4ca0c5
-- title:
--   Val Gen Extend: mem basic Open of mem
-- statement:
--   The Val Gen Extend construction uses the mem basic Open of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorExtendsFromGenericFibreValuationRing.lean#L45-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeneratorExtendsFromGenericFibreValuationRing.lean#L45-L52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeneratorExtendsFromGenericFibreValuationRing
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
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.ValGenExtend

theorem GlobalTheory.ValGenExtend.mem_basicOpen_of_mem {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) {i : L.ι} (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by sorry
