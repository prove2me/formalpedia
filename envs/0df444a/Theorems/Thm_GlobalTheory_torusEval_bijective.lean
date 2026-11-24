-- Prove2me | Theorems.Thm_GlobalTheory_torusEval_bijective
-- name    : GlobalTheory.torusEval_bijective
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:23:35.792683+00:00
-- url     : https://prove2.me/theorems/c90ac2a8-8790-4b41-a0b0-c7cb6db32f6b
-- title:
--   Global Theory: torus Eval bijective
-- statement:
--   The Global Theory construction uses the torus Eval bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L124-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L124-L134

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
variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X]

theorem GlobalTheory.torusEval_bijective :
    Function.Bijective (torusEval : (Multiplicative X →* Rˣ) → (AddMonoidAlgebra R X →ₐ[R] R)) := by sorry
