-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_sum_reverse_eq_zero
-- name    : GlobalTheory.CompanionTheory.HeckeTransfer.sum_reverse_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:59:23.984746+00:00
-- url     : https://prove2.me/theorems/787f0d0e-0579-4872-be62-53965146d718
-- title:
--   Hecke Transfer: sum reverse eq zero
-- statement:
--   The Hecke Transfer construction uses the sum reverse eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L26-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L26-L64

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeTransfer
variable {R : Type*} [Ring R]

theorem GlobalTheory.CompanionTheory.HeckeTransfer.sum_reverse_eq_zero {M : ℕ} (b : Fin M → R) (h : stdPoly (1 : R) b = 0) :
    ∑ π : Equiv.Perm (Fin M), (Equiv.Perm.sign π : ℤ) • (List.ofFn fun i => b (π i)).reverse.prod = 0 := by sorry
