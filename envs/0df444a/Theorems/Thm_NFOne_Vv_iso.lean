-- Prove2me | Theorems.Thm_NFOne_Vv_iso
-- name    : NFOne.Vv_iso
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:17.948823+00:00
-- url     : https://prove2.me/theorems/c251f2a1-cd4f-4836-b541-eafe70998750
-- title:
--   NFOne: Vv iso
-- statement:
--   The NFOne construction uses the Vv iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L51-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L51-L56

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

theorem NFOne.Vv_iso (k r j : ℕ) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (N : Matrix (Fin j) (Fin j) ℂ)
    (hyy : ∀ a a', herm (Hpk k r) (y a) (y a') = 0) (b c : ℕ) (hb : b < j) (hc : c < j) :
    herm (Hpk k r) (Vv y N b) (Vv y N c) = 0 := by sorry
