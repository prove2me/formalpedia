-- Prove2me | Theorems.Thm_GlobalTheory_torusCoord_apply
-- name    : GlobalTheory.torusCoord_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:10.514751+00:00
-- url     : https://prove2.me/theorems/7357ae9f-e385-47e2-91ba-b0d0d391324d
-- title:
--   Global Theory: torus Coord apply
-- statement:
--   The Global Theory construction uses the torus Coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L326-L327
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L326-L327

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

theorem GlobalTheory.torusCoord_apply (b : Module.Basis ι ℤ X) (t : Multiplicative X →* Rˣ) (i : ι) :
    torusCoord R b t i = t (Multiplicative.ofAdd (b i)) := by sorry

attribute [defeq] GlobalTheory.torusCoord_apply
