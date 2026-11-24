-- Prove2me | Theorems.Thm_GlobalTheory_exists_basis_closure_eq_of_fg_of_nsmul_mem
-- name    : GlobalTheory.exists_basis_closure_eq_of_fg_of_nsmul_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:28.148039+00:00
-- url     : https://prove2.me/theorems/3f9c12d1-6b29-474b-99ed-b8cb5f73fbcf
-- title:
--   Global Theory: exists basis closure eq of fg of nsmul mem
-- statement:
--   The Global Theory construction uses the exists basis closure eq of fg of nsmul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexMapNsmulComapEqAbsNormDet.lean#L7-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RelIndexMapNsmulComapEqAbsNormDet.lean#L7-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexMapNsmulComapEqAbsNormDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open GlobalTheory

theorem GlobalTheory.exists_basis_closure_eq_of_fg_of_nsmul_mem {Γ : Type} [AddCommGroup Γ] [Module ℚ Γ]
    (A : AddSubgroup Γ) (hA : A.FG) (hN : ∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℚ Γ), A = AddSubgroup.closure (Set.range b) := by sorry
