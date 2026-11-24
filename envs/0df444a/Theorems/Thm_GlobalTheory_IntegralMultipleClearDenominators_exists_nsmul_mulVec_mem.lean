-- Prove2me | Theorems.Thm_GlobalTheory_IntegralMultipleClearDenominators_exists_nsmul_mulVec_mem
-- name    : GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:04.884701+00:00
-- url     : https://prove2.me/theorems/002dfe68-685f-4251-ab67-87e25b2263b9
-- title:
--   Integral Multiple Clear Denominators: exists nsmul mul Vec mem
-- statement:
--   The Integral Multiple Clear Denominators construction uses the exists nsmul mul Vec mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNsmulMulVecMem.lean#L53-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNsmulMulVecMem.lean#L53-L73

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

theorem GlobalTheory.IntegralMultipleClearDenominators.exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • Matrix.mulVec M v ∈ L := by sorry
