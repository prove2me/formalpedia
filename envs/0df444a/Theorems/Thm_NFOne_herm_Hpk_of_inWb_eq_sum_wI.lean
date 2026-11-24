-- Prove2me | Theorems.Thm_NFOne_herm_Hpk_of_inWb_eq_sum_wI
-- name    : NFOne.herm_Hpk_of_inWb_eq_sum_wI
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:10.614848+00:00
-- url     : https://prove2.me/theorems/8e73bc51-4bc0-4e3f-bd7b-964118a4ed0f
-- title:
--   NFOne: herm Hpk of in Wb eq sum w I
-- statement:
--   The NFOne construction uses the herm Hpk of in Wb eq sum w I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L40-L44

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

theorem NFOne.herm_Hpk_of_inWb_eq_sum_wI (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r + k + 1) → ℂ)
    (hzy : ∀ a, herm (Hpk k r) z' (y a) = 0) (β : Fin j → ℂ) :
    herm (Hpk k r) z' (∑ a, β a • y a) = 0 := by sorry
