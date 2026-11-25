-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_LieCharpolyRootPairs_IsRootPair_side
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs.IsRootPair.side
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:46.717753+00:00
-- url     : https://prove2.me/theorems/9ffadad3-1893-4b04-8f89-657c89098b68
-- title:
--   Is Root Pair: side
-- statement:
--   The Is Root Pair construction uses the side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LieCharpolyRootPairs.lean#L109-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/LieCharpolyRootPairs.lean#L109-L120

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.LieCharpolyRootPairs.IsRootPair.side [CharZero k] {s : O} {δ : k} (h : IsRootPair s δ) (τ : O →+* k) :
    Xor' (τ s = δ) (τ s = -δ) := by sorry
