-- Prove2me | Theorems.Thm_GlobalTheory_isClosed_torusZariski_iff
-- name    : GlobalTheory.isClosed_torusZariski_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:50.887796+00:00
-- url     : https://prove2.me/theorems/b60b4557-4920-4e8e-99e9-e7f3a75e1b38
-- title:
--   Global Theory: is Closed torus Zariski iff
-- statement:
--   The Global Theory construction uses the is Closed torus Zariski iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L171-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L171-L182

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
variable [IsDomain R]

theorem GlobalTheory.isClosed_torusZariski_iff (H : Set (Multiplicative X →* Rˣ)) :
    IsClosed[torusZariski R X] H ↔
      ∃ S : Set (AddMonoidAlgebra R X), ∀ t, t ∈ H ↔ ∀ f ∈ S, torusEval t f = 0 := by sorry
