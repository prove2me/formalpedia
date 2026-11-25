-- Prove2me | Theorems.Thm_NFOne_hermitian_orthogonal_projection_vector
-- name    : NFOne.hermitian_orthogonal_projection_vector
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:21.046738+00:00
-- url     : https://prove2.me/theorems/0d8b4721-7e96-4415-bb68-764e8a24a383
-- title:
--   NFOne: hermitian orthogonal projection vector
-- statement:
--   The NFOne construction uses the hermitian orthogonal projection vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L58-L64

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

theorem NFOne.hermitian_orthogonal_projection_vector (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ)
    (z' : Fin (2 * r + k + 1) → ℂ) (hzy : ∀ a, herm (Hpk k r) z' (y a) = 0) (c : ℕ) :
    herm (Hpk k r) z' (Vv y N c) = 0 := by sorry
