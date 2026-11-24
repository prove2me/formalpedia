-- Prove2me | Theorems.Thm_GlobalTheory_mem_of_isClosed_torusZariski
-- name    : GlobalTheory.mem_of_isClosed_torusZariski
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:11:17.914212+00:00
-- url     : https://prove2.me/theorems/792a0e85-9f2c-4c06-be30-23e2b50462fc
-- title:
--   Global Theory: mem of is Closed torus Zariski
-- statement:
--   The Global Theory construction uses the mem of is Closed torus Zariski property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L199-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L199-L204

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

theorem GlobalTheory.mem_of_isClosed_torusZariski {H : Subgroup (Multiplicative X →* Rˣ)}
    (hH : IsClosed[torusZariski R X] (H : Set (Multiplicative X →* Rˣ)))
    {t : Multiplicative X →* Rˣ}
    (ht : ∀ x : Multiplicative X, (∀ s ∈ H, s x = 1) → t x = 1) : t ∈ H := by sorry
