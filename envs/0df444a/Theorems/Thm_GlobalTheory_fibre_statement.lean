-- Prove2me | Theorems.Thm_GlobalTheory_fibre_statement
-- name    : GlobalTheory.fibre_statement
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:55:29.137842+00:00
-- url     : https://prove2.me/theorems/d8244db5-d701-57b5-8fb0-8f9a788311dc
-- title:
--   Global Theory: fibre statement
-- statement:
--   The Global Theory construction uses the fibre statement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOne.lean#L116-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupMulPUnitFibreEqLevelOne.lean#L116-L196

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOne
import Theorems.Thm_GlobalTheory_IsBicharacter_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra GlobalTheory.PDiv
open GlobalTheory
open scoped TensorProduct
set_option autoImplicit false
open TensorProduct Coalgebra Bialgebra

theorem GlobalTheory.fibre_statement : ∀ (p : ℕ) (R k : Type) [CommRing R] [CommRing k]
    [Algebra R k], Function.Surjective (algebraMap R k) → ∀ (G : _root_.GlobalTheory.PDivGroup p R) (n : ℕ),
      Function.Surjective (fun a : G.A (n + 1) =>
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1)) ∧
      ∀ a : G.A (n + 1),
        ((1 : k) ⊗ₜ[R] G.resOne n a : k ⊗[R] G.A 1) = 0 ↔
          a ∈ (RingHom.ker ((algebraMap R k).comp
            (Bialgebra.counitAlgHom R (G.A n) :
              G.A n →+* R))).map
            ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) :
              G.A n →+* G.A (n + 1)) := by sorry
