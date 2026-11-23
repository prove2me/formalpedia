-- Prove2me | Theorems.Thm_MassDataIdxSpl_snd_apply_alt
-- name    : MassDataIdxSpl.snd_apply_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:31.684156+00:00
-- url     : https://prove2.me/theorems/4928279d-4c9c-471d-a030-b8fd3e40ff70
-- title:
--   Mass Data Idx Spl: snd apply alt
-- statement:
--   The Mass Data Idx Spl construction uses the snd apply alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L46-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L46-L46

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

theorem MassDataIdxSpl.snd_apply_alt (v : n → T) (i : n) : pr2 θ v i = (θ (v i)).2 := by sorry
