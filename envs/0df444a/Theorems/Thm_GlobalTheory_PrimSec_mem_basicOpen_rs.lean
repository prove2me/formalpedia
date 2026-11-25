-- Prove2me | Theorems.Thm_GlobalTheory_PrimSec_mem_basicOpen_rs
-- name    : GlobalTheory.PrimSec.mem_basicOpen_rs
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:57:40.730115+00:00
-- url     : https://prove2.me/theorems/55da69af-aaca-4972-b401-15724c40cf85
-- title:
--   Prim Sec: mem basic Open rs
-- statement:
--   The Prim Sec construction uses the mem basic Open rs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsSmulSecNonzeroOnSpecialFibre.lean#L50-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingExistsAssociatedOfSumEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulSecNonzeroOnSpecialFibre
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
noncomputable section
open GlobalTheory GlobalTheory.PrimSec
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem GlobalTheory.PrimSec.mem_basicOpen_rs {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) {x : X} (hx : x ∈ V) :
    x ∈ X.basicOpen (rs X h a) ↔ x ∈ X.basicOpen a := by sorry
