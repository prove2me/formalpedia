-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_RamifiedPlacesSplitEigen_lieMult_iff
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen.lieMult_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:35:48.063089+00:00
-- url     : https://prove2.me/theorems/2feef231-ab0c-47d0-a18e-342cfa56d60c
-- title:
--   Ramified Places Split Eigen: lie Mult iff
-- statement:
--   The Ramified Places Split Eigen construction uses the lie Mult iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/RamifiedPlacesSplitEigen.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/RamifiedPlacesSplitEigen.lean#L35-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_RamifiedPlacesSplitEigen
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
  IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen
variable {S : Scheme.{0}} {R : Type} [CommRing R]
variable {O : Type} [CommRing O] {G : Over S} [GrpObj G]

theorem GlobalTheory.IndefiniteRowSideFullHecke.RamifiedPlacesSplitEigen.lieMult_iff {k : Type} [Field k] (act : OAct O G) (t : Sp k ⟶ S) (χ : O →+* k) (n : ℕ) :
    LieMult act t χ n ↔ ∃ v : Fin n → (epsAt t ⟶ G), IsEigBasis act t χ v := by sorry
