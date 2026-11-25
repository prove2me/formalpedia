-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LieCharpolyRootPairs_DetCond_swap
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs.DetCond.swap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:22.755804+00:00
-- url     : https://prove2.me/theorems/d06fa90d-c656-4ae0-a3d5-704f69340a88
-- title:
--   Det Cond: swap
-- statement:
--   The Det Cond construction uses the swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LieCharpolyRootPairs.lean#L122-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LieCharpolyRootPairs.lean#L122-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LieCharpolyRootPairs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial
variable {S : Scheme.{0}} {k : Type} [Field k]
variable (G : Over S) [GrpObj G]
variable {G}
variable {O : Type} [CommRing O]
variable [IsCommMonObj G]

theorem GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs.DetCond.swap [IsAlgClosed k] [CharZero k] {ρ : OAct O G} {t : Spec (CommRingCat.of k) ⟶ S}
    {s : O} {δ : k} {p q : ℕ} (h : DetCond ρ t s δ p q) : DetCond ρ t s (-δ) q p := by sorry
