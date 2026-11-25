-- Prove2me | Theorems.Thm_MassDataIdxSpl_fst_mem_span_alt
-- name    : MassDataIdxSpl.fst_mem_span_alt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:42.853931+00:00
-- url     : https://prove2.me/theorems/a1f3feae-47f5-412e-ae64-47d5f6836065
-- title:
--   Mass Data Idx Spl: fst mem span alt
-- statement:
--   The Mass Data Idx Spl construction uses the fst mem span alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L79-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L79-L87

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

theorem MassDataIdxSpl.fst_mem_span_alt {v : n → T} (hv : v ∈ Submodule.span T (Y '' s)) :
    pr1 θ v ∈ Submodule.span K ((fun a => pr1 θ (Y a)) '' s) := by sorry
