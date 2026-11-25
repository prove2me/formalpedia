-- Prove2me | Theorems.Thm_GlobalTheory_Mem_NrmCompl_nrmAbs_le_one_iff
-- name    : GlobalTheory.Mem.NrmCompl.nrmAbs_le_one_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:54.435072+00:00
-- url     : https://prove2.me/theorems/07247bbc-0e16-5281-b35f-26ae1932dd75
-- title:
--   Nrm Compl: nrm Abs le one iff
-- statement:
--   The Nrm Compl construction uses the nrm Abs le one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NrmAbsOfValuationEqExp.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NrmAbsOfValuationEqExp.lean#L36-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NrmAbsOfValuationEqExp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.NrmCompl
open NumberField IsDedekindDomain
variable {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))

theorem GlobalTheory.Mem.NrmCompl.nrmAbs_le_one_iff (x : P.adicCompletion L) : nrmAbs P x ≤ 1 ↔ Valued.v x ≤ 1 := by sorry
