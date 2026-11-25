-- Prove2me | Theorems.Thm_GlobalTheory_Mem_NrmCompl_continuous_nrmAbs
-- name    : GlobalTheory.Mem.NrmCompl.continuous_nrmAbs
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:13.718075+00:00
-- url     : https://prove2.me/theorems/d025b43c-b70b-49f0-8f73-a2c9ce334aef
-- title:
--   Nrm Compl: continuous nrm Abs
-- statement:
--   The Nrm Compl construction uses the continuous nrm Abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NrmAbsOfValuationEqExp.lean#L44-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NrmAbsOfValuationEqExp.lean#L44-L44

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

theorem GlobalTheory.Mem.NrmCompl.continuous_nrmAbs : Continuous (nrmAbs P) := by sorry
