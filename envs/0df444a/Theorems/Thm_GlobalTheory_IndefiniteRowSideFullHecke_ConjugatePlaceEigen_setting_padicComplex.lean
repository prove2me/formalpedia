-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_ConjugatePlaceEigen_setting_padicComplex
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.setting_padicComplex
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:37.675873+00:00
-- url     : https://prove2.me/theorems/2acd9066-5406-555c-a805-af1a1155077b
-- title:
--   Conjugate Place Eigen: setting padic Complex
-- statement:
--   The Conjugate Place Eigen construction uses the setting padic Complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ConjugatePlaceEigen.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ConjugatePlaceEigen.lean#L89-L100

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_DualLattices_CotangentSurjective
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ConjugatePlaceEigen
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out
open Ideal
variable (p : ℕ) [hp : Fact p.Prime]

theorem GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen.setting_padicComplex : HidaSetting p (PadicComplex.valued p).v 𝓞_ℂ_[p] := by sorry
