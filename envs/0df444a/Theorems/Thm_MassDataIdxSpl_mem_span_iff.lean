-- Prove2me | Theorems.Thm_MassDataIdxSpl_mem_span_iff
-- name    : MassDataIdxSpl.mem_span_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:03:33.210257+00:00
-- url     : https://prove2.me/theorems/66970912-63f4-53c4-b738-7d57d31a5dd0
-- title:
--   Mass Data Idx Spl: mem span iff
-- statement:
--   The Mass Data Idx Spl construction uses the mem span iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L121-L126

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

theorem MassDataIdxSpl.mem_span_iff (v : n → T) :
    v ∈ Submodule.span T (Y '' s) ↔ pr1 θ v ∈ Submodule.span K ((fun a => pr1 θ (Y a)) '' s) ∧
      pr2 θ v ∈ Submodule.span K ((fun a => pr2 θ (Y a)) '' s) := by sorry
