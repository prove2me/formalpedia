-- Prove2me | Theorems.Thm_NFOne_Vv_zero
-- name    : NFOne.Vv_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:27.644904+00:00
-- url     : https://prove2.me/theorems/338a8945-429a-4385-aed9-48f8be96921d
-- title:
--   NFOne: Vv zero
-- statement:
--   The NFOne construction uses the Vv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L46-L49

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

theorem NFOne.Vv_zero {k r j : ℕ} (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ)
    (c : ℕ) (hc : j ≤ c) : Vv y N c = 0 := by sorry
