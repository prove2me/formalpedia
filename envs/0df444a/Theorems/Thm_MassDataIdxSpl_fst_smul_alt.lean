-- Prove2me | Theorems.Thm_MassDataIdxSpl_fst_smul_alt
-- name    : MassDataIdxSpl.fst_smul_alt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:37.588067+00:00
-- url     : https://prove2.me/theorems/ad07fb21-5e4f-4b53-9a21-37fb828e7def
-- title:
--   Mass Data Idx Spl: fst smul alt
-- statement:
--   The Mass Data Idx Spl construction uses the fst smul alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L67-L70

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

theorem MassDataIdxSpl.fst_smul_alt (c : T) (v : n → T) : pr1 θ (c • v) = (θ c).1 • pr1 θ v := by sorry
