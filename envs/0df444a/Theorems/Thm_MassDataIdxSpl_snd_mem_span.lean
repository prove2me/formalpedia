-- Prove2me | Theorems.Thm_MassDataIdxSpl_snd_mem_span
-- name    : MassDataIdxSpl.snd_mem_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:41.243545+00:00
-- url     : https://prove2.me/theorems/c312f4c8-58c5-4ace-b3ed-cf7e76196238
-- title:
--   Mass Data Idx Spl: snd mem span
-- statement:
--   The Mass Data Idx Spl construction uses the snd mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L89-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L89-L97

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_FstMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxSpl
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
variable {ι : Type} (Y : ι → n → T) (s : Set ι)

theorem MassDataIdxSpl.snd_mem_span {v : n → T} (hv : v ∈ Submodule.span T (Y '' s)) :
    pr2 θ v ∈ Submodule.span K ((fun a => pr2 θ (Y a)) '' s) := by sorry
