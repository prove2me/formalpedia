-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FramedFlatCoordinates_lieMult_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.lieMult_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:03:01.937818+00:00
-- url     : https://prove2.me/theorems/0ef1c64f-9cb0-5ae2-9b0e-bc2d03df3211
-- title:
--   Framed Flat Coordinates: lie Mult iff
-- statement:
--   The Framed Flat Coordinates construction uses the lie Mult iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/FramedFlatCoordinates.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/FramedFlatCoordinates.lean#L36-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPushEquiv
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_FramedFlatCoordinates
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R]

theorem GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates.lieMult_iff {k : Type} [Field k] {O : Type} [CommRing O] (act : OAct O G) (x : Sp k ⟶ S)
    (χ : O →+* k) (n : ℕ) :
    LieMult act x χ n ↔ ∃ v : Fin n → (epsAt x ⟶ G), IsEigenBasis act x χ v := by sorry
