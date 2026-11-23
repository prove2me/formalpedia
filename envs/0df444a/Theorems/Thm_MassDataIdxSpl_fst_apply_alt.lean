-- Prove2me | Theorems.Thm_MassDataIdxSpl_fst_apply_alt
-- name    : MassDataIdxSpl.fst_apply_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:19.76869+00:00
-- url     : https://prove2.me/theorems/ec26dc22-2030-4299-99a5-8ad40fc8725c
-- title:
--   Mass Data Idx Spl: fst apply alt
-- statement:
--   The Mass Data Idx Spl construction uses the fst apply alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L45-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/FstMemSpan.lean#L45-L45

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

theorem MassDataIdxSpl.fst_apply_alt (v : n → T) (i : n) : pr1 θ v i = (θ (v i)).1 := by sorry
