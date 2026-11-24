-- Prove2me | Theorems.Thm_GlobalTheory_ClassFin_isLog_kronecker
-- name    : GlobalTheory.ClassFin.isLog_kronecker
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:11:51.343833+00:00
-- url     : https://prove2.me/theorems/32da5f75-1546-4d1e-9c9c-2ee6830f6705
-- title:
--   Class Fin: is Log kronecker
-- statement:
--   The Class Fin construction uses the is Log kronecker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsLogKronecker.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsLogKronecker.lean#L8-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsLogKronecker
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

theorem GlobalTheory.ClassFin.isLog_kronecker {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} [Fintype κ] [DecidableEq κ]
    {H A : Matrix ι ι ℂ} {H' A' : Matrix κ κ ℂ} (h : IsLog H A) (h' : IsLog H' A') :
    IsLog (H ⊗ₖ (1 : Matrix κ κ ℂ) + (1 : Matrix ι ι ℂ) ⊗ₖ H') (A ⊗ₖ A') := by sorry
