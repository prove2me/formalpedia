-- Prove2me | Theorems.Thm_NFOne_cols_X
-- name    : NFOne.cols_X
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:48.353247+00:00
-- url     : https://prove2.me/theorems/2be70f99-68a5-4ff7-8369-c3b9b4687be7
-- title:
--   NFOne: cols X
-- statement:
--   The NFOne construction uses the cols X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L185-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L185-L196

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

theorem NFOne.cols_X (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (1 + Pm k r j V) *ᵥ bvec (eI k r a) = bvec (eI k r a) := by sorry
