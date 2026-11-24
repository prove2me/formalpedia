-- Prove2me | Theorems.Thm_GlobalTheory_torusCoord_symm_apply
-- name    : GlobalTheory.torusCoord_symm_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:52.021856+00:00
-- url     : https://prove2.me/theorems/74e4aa9b-9762-492d-8e83-1643428dab84
-- title:
--   Global Theory: torus Coord symm apply
-- statement:
--   The Global Theory construction uses the torus Coord symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L329-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L329-L333

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteOfIsClosedTorusZariskiOfPowEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology
open GlobalTheory
open AddMonoidAlgebra
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] {ι : Type*}

theorem GlobalTheory.torusCoord_symm_apply (b : Module.Basis ι ℤ X) (u : ι → Rˣ) (x : X) :
    (torusCoord R b).symm u (Multiplicative.ofAdd x) = (b.repr x).prod fun i m => u i ^ m := by sorry
