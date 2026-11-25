-- Prove2me | Theorems.Thm_MassDataIdxSpl_snd_smul_alt
-- name    : MassDataIdxSpl.snd_smul_alt
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:51:33.993941+00:00
-- url     : https://prove2.me/theorems/12e8a375-5c2b-4a41-9e56-453b0777da04
-- title:
--   Mass Data Idx Spl: snd smul alt
-- statement:
--   The Mass Data Idx Spl construction uses the snd smul alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L72-L75

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

theorem MassDataIdxSpl.snd_smul_alt (c : T) (v : n → T) : pr2 θ (c • v) = (θ c).2 • pr2 θ v := by sorry
