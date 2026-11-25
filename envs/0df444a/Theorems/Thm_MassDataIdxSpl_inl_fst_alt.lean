-- Prove2me | Theorems.Thm_MassDataIdxSpl_inl_fst_alt
-- name    : MassDataIdxSpl.inl_fst_alt
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:45.235851+00:00
-- url     : https://prove2.me/theorems/57868c6e-b8ab-46d7-b780-4f788a0d6fb1
-- title:
--   Mass Data Idx Spl: inl fst alt
-- statement:
--   The Mass Data Idx Spl construction uses the inl fst alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L53-L58

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

theorem MassDataIdxSpl.inl_fst_alt (v : n → T) : inj1 θ (pr1 θ v) = θ.symm (1, 0) • v := by sorry
