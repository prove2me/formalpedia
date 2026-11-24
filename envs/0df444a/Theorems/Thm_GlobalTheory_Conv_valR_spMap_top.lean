-- Prove2me | Theorems.Thm_GlobalTheory_Conv_valR_spMap_top
-- name    : GlobalTheory.Conv.valR_spMap_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:34:16.119977+00:00
-- url     : https://prove2.me/theorems/45644f8d-ec6d-449d-9867-2c42ca16f5a9
-- title:
--   Conv: val R sp Map top
-- statement:
--   The Conv construction uses the val R sp Map top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L28-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_EqZeroOfForallExistsLsumETwoPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSumsAtHalfCurveFraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Filter Topology
open scoped PowerSeries LaurentSeries
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HolHom
open GlobalTheory GlobalTheory.Conv
variable {A : Type} [CommRing A] {Z : Scheme.{0}}

theorem GlobalTheory.Conv.valR_spMap_top {O : Type} [CommRing O] (β : O →+* A) (a : O) :
    valR (spMap β) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a) = β a := by sorry
