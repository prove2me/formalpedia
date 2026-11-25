-- Prove2me | Theorems.Thm_MassDataIdxSpl_inr_snd_alt
-- name    : MassDataIdxSpl.inr_snd_alt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:38.104475+00:00
-- url     : https://prove2.me/theorems/87aa4ce0-af41-4810-a1b5-5c06342b62eb
-- title:
--   Mass Data Idx Spl: inr snd alt
-- statement:
--   The Mass Data Idx Spl construction uses the inr snd alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L60-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L60-L65

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

theorem MassDataIdxSpl.inr_snd_alt (v : n → T) : inj2 θ (pr2 θ v) = θ.symm (0, 1) • v := by sorry
