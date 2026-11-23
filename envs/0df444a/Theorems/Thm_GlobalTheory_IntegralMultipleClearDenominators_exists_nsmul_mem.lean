-- Prove2me | Theorems.Thm_GlobalTheory_IntegralMultipleClearDenominators_exists_nsmul_mem
-- name    : GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:43:20.3363+00:00
-- url     : https://prove2.me/theorems/d43ff033-e30f-49b6-853f-ef136a9e2618
-- title:
--   Integral Multiple Clear Denominators: exists nsmul mem
-- statement:
--   The Integral Multiple Clear Denominators construction uses the exists nsmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNsmulMulVecMem.lean#L25-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNsmulMulVecMem.lean#L25-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultipleClearDenominators
open NumberField

theorem GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ L := by sorry
