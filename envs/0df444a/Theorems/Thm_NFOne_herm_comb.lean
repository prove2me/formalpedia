-- Prove2me | Theorems.Thm_NFOne_herm_comb
-- name    : NFOne.herm_comb
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:48:07.51339+00:00
-- url     : https://prove2.me/theorems/b040f71b-d356-4572-82f0-7d243ee4ea65
-- title:
--   NFOne: herm comb
-- statement:
--   The NFOne construction uses the herm comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L32-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L32-L38

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_HermitianOrthogonalProjectionVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants Formalism.FourierDecayAlt.C3
noncomputable section
open NFOne

theorem NFOne.herm_comb (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hyy : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (α β : Fin j → ℂ) :
    herm (Hpk k r) (∑ a, α a • y a) (∑ a, β a • y a) = 0 := by sorry
