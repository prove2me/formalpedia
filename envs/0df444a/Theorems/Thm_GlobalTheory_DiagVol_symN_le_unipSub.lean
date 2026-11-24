-- Prove2me | Theorems.Thm_GlobalTheory_DiagVol_symN_le_unipSub
-- name    : GlobalTheory.DiagVol.symN_le_unipSub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:50:01.419721+00:00
-- url     : https://prove2.me/theorems/2241b9fb-fbd7-4fff-addf-a4c54d23a870
-- title:
--   Diag Vol: sym N le unip Sub
-- statement:
--   The Diag Vol construction uses the sym N le unip Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEq.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInverseUnipotentVolumeConjDiagonalEq.lean#L48-L51

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

theorem GlobalTheory.DiagVol.symN_le_unipSub {F : Type} [Field F] : symN F n c ≤ unipSub (ordL c) := by sorry
