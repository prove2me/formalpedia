-- Prove2me | Theorems.Thm_GlobalTheory_IntegralMultipleOfVectors_exists_nsmul_mem
-- name    : GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:20:55.455675+00:00
-- url     : https://prove2.me/theorems/c0a5174e-d7da-48c4-960f-6fd92ac3c5e4
-- title:
--   Integral Multiple Of Vectors: exists nsmul mem
-- statement:
--   The Integral Multiple Of Vectors construction uses the exists nsmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNsmulMem.lean#L24-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNsmulMem.lean#L24-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.IntegralMultipleOfVectors

theorem GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • w ∈ L := by sorry
