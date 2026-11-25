-- Prove2me | Theorems.Thm_MassDataIdxCore_map_sub_one
-- name    : MassDataIdxCore.map_sub_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:36:45.154821+00:00
-- url     : https://prove2.me/theorems/ce0b09f4-00cf-4bd8-aedf-f7bb525b766a
-- title:
--   Mass Data Idx Core: map sub one
-- statement:
--   The Mass Data Idx Core construction uses the map sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitSmul.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeIndices/SecondSplitSmul.lean#L16-L18

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_PsiKerIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeIndices_SecondSplitSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MassDataIdxCore
open Matrix
variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (O : ValuationSubring K) {n : Type} [Fintype n]
  [DecidableEq n] (θ : T ≃ₐ[K] K × K) (s : T →+* T) (J : Matrix n n T) (P : GL n K)

theorem MassDataIdxCore.map_sub_one (M : Matrix n n T) (f : T →+* K) : (M - 1).map f = M.map f - 1 := by sorry
