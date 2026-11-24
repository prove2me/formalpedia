-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_conj_diag_mem
-- name    : GlobalTheory.DiagVol.conj_diag_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:20.098216+00:00
-- url     : https://prove2.me/theorems/69da6d23-db61-4cff-aaa6-241d46bfc33e
-- title:
--   Diag Vol: conj diag mem
-- statement:
--   The Diag Vol construction uses the conj diag mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEq.lean#L53-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEq.lean#L53-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrdL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLColumnCongruenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexConjIntegralGLRowCongruenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInverseUnipotentVolumeConjDiagonalEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.DiagVol
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.DiagVol.conj_diag_mem {F : Type} [Field F] (d : n ⊕ Fin c → Fˣ) {x : GL (n ⊕ Fin c) F} (hx : x ∈ symN F n c) :
    diagGL d * x * (diagGL d)⁻¹ ∈ symN F n c := by sorry
