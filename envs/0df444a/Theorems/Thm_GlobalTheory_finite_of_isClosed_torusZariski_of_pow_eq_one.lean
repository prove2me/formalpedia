-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_isClosed_torusZariski_of_pow_eq_one
-- name    : GlobalTheory.finite_of_isClosed_torusZariski_of_pow_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:47:03.020417+00:00
-- url     : https://prove2.me/theorems/dbd29deb-04a2-4d07-a6e1-cad676aae0c7
-- title:
--   Global Theory: finite of is Closed torus Zariski of pow eq one
-- statement:
--   The Global Theory construction uses the finite of is Closed torus Zariski of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L265-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteOfIsClosedTorusZariskiOfPowEqOne.lean#L265-L286

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

theorem GlobalTheory.finite_of_isClosed_torusZariski_of_pow_eq_one [Module.Finite ℤ X] {n : ℕ} (h2 : 2 ≤ n)
    [HasEnoughRootsOfUnity R n] {H : Subgroup (Multiplicative X →* Rˣ)}
    (hH : IsClosed[torusZariski R X] (H : Set (Multiplicative X →* Rˣ)))
    (hn : ∀ s ∈ H, s ^ n = 1 → s = 1) : Finite H ∧ (Nat.card H).Coprime n := by sorry
