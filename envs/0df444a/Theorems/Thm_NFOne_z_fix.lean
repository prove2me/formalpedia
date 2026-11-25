-- Prove2me | Theorems.Thm_NFOne_z_fix
-- name    : NFOne.z_fix
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:34.764086+00:00
-- url     : https://prove2.me/theorems/7b0ccb5b-343d-4f58-87a2-90a5dd6e3795
-- title:
--   NFOne: z fix
-- statement:
--   The NFOne construction uses the z fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L198-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L198-L224

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

theorem NFOne.z_fix (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z') (Vz : ∀ c, herm (Hpk k r) z' (V c) = 0) :
    (1 + Pm k r j V) *ᵥ z' = z' := by sorry
