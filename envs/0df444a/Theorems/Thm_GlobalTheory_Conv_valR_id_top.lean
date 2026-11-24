-- Prove2me | Theorems.Thm_GlobalTheory_Conv_valR_id_top
-- name    : GlobalTheory.Conv.valR_id_top
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:27:10.593009+00:00
-- url     : https://prove2.me/theorems/7cecf80b-9d77-4925-b5fe-c035662f480d
-- title:
--   Conv: val R id top
-- statement:
--   The Conv construction uses the val R id top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsSumsAtHalfCurveFraction.lean#L18-L26

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

theorem GlobalTheory.Conv.valR_id_top (a : A) :
    valR (𝟙 (Sp A)) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) = a := by sorry
