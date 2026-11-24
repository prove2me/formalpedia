-- Prove2me | Theorems.Thm_NFOne_y_esI_zero
-- name    : NFOne.y_esI_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:47:27.464444+00:00
-- url     : https://prove2.me/theorems/841d0f5b-73a6-4c7f-b794-e41892fbc538
-- title:
--   NFOne: y es I zero
-- statement:
--   The NFOne construction uses the y es I zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L66-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L66-L78

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

theorem NFOne.y_esI_zero (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (a : Fin j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) (hb : ¬ (sg k r q).val < j) :
    y a q = 0 := by sorry
