-- Prove2me | Theorems.Thm_GlobalTheory_DualTransfer_finite_quot
-- name    : GlobalTheory.DualTransfer.finite_quot
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:52:07.745592+00:00
-- url     : https://prove2.me/theorems/eb81c2ce-cdb8-4a52-a6e8-b2b49d94c7ea
-- title:
--   Dual Transfer: finite quot
-- statement:
--   The Dual Transfer construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DivisiblePontryaginAnnihilatorDuality.lean#L97-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DivisiblePontryaginAnnihilatorDuality.lean#L97-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DivisiblePontryaginAnnihilatorDuality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DualTransfer

theorem GlobalTheory.DualTransfer.finite_quot {G : Type} [AddCommGroup G] (A L₀ : AddSubgroup G) (N : ℕ) (hN : 0 < N)
    (tf : Function.Injective fun t : G => N • t)
    (hA : ∀ t ∈ A, N • t ∈ L₀)
    (fin : ∀ k : ℕ, 0 < k → ∃ R : Set G, R.Finite ∧ ∀ t ∈ L₀, ∃ r ∈ R, ∃ u ∈ L₀, t = r + k • u) :
    Finite (A ⧸ (L₀.map (nsmulAddMonoidHom N)).addSubgroupOf A) := by sorry
