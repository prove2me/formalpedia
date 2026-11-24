-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_invVol_diag_one
-- name    : GlobalTheory.DiagVol.invVol_diag_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:49:57.000434+00:00
-- url     : https://prove2.me/theorems/16ee40b7-9fef-4837-a765-fe9dbfebe4b8
-- title:
--   Diag Vol: inv Vol diag one
-- statement:
--   The Diag Vol construction uses the inv Vol diag one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEq.lean#L71-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEq.lean#L71-L114

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.DiagVol.invVol_diag_one (ϖ : kˣ) (hϖ : IsUnif ϖ) (t : n ⊕ Fin c) :
    ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) =
      (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by sorry
