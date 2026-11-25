-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_EpsilonPointMorphisms_Unif_IsSec_add_lat
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif.IsSec.add_lat
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:10:07.290256+00:00
-- url     : https://prove2.me/theorems/ba62b53a-fdfc-5bc2-a112-43e255a1b26c
-- title:
--   Is Sec: add lat
-- statement:
--   The Is Sec construction uses the add lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean#L175-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/ExponentialDifferential.lean#L175-L190

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_ExponentialDifferential
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms
open GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (F : Unif A L g)

theorem GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPointMorphisms.Unif.IsSec.add_lat {F : Unif A L g} {a : F.toExp.lat → (Fin g → ℂ) → ℂ} (ha : F.HasFactor a) {s : L.Sec}
    {θ : (Fin g → ℂ) → ℂ} (hs : F.IsSec s θ) (la : F.toExp.lat) (z : Fin g → ℂ) :
    θ (z + la) = a la z * θ z := by sorry
