-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_ss_transfer
-- name    : GlobalTheory.ClassFin.ss_transfer
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:11:12.146026+00:00
-- url     : https://prove2.me/theorems/c57792fb-82a2-4d49-b661-c5967b8286a1
-- title:
--   Class Fin: ss transfer
-- statement:
--   The Class Fin construction uses the ss transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SsTransfer.lean#L8-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/SsTransfer.lean#L8-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SsTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.ClassFin

theorem GlobalTheory.ClassFin.ss_transfer : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S Γ : Set (Matrix ι ι ℂ)), (S ⊆ Γ → Γ ⊆ (Submodule.span ℂ S : Set (Matrix ι ι ℂ)) → SS S → SS Γ) ∧ ∀ P : Matrix ι ι ℂ, IsUnit P.det → SS ((fun x => P * x * P⁻¹) '' S) → SS S := by sorry
