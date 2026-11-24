-- Prove2me | Theorems.Thm_GlobalTheory_Mem_NrmCompl_nrmAbs_eq_zpow
-- name    : GlobalTheory.Mem.NrmCompl.nrmAbs_eq_zpow
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:23:47.640881+00:00
-- url     : https://prove2.me/theorems/77cfa392-9b87-4a53-bcd7-dbdeb47602d3
-- title:
--   Nrm Compl: nrm Abs eq zpow
-- statement:
--   The Nrm Compl construction uses the nrm Abs eq zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NrmAbsOfValuationEqExp.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NrmAbsOfValuationEqExp.lean#L19-L26

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

theorem GlobalTheory.Mem.NrmCompl.nrmAbs_eq_zpow {x : P.adicCompletion L} (hx : x ≠ 0) :
    nrmAbs P x = (Ideal.absNorm P.asIdeal : ℝ) ^ (WithZero.log (Valued.v x)) := by sorry
