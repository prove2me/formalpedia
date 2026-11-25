-- Prove2me | Theorems.Thm_NFOne_projection_vector_coordinate
-- name    : NFOne.projection_vector_coordinate
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:42.534382+00:00
-- url     : https://prove2.me/theorems/56bb7daa-24d6-4c4c-8be8-8c68bab17a1a
-- title:
--   NFOne: projection vector coordinate
-- statement:
--   The NFOne construction uses the projection vector coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L80-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L80-L103

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

theorem NFOne.projection_vector_coordinate (k r j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (N : Matrix (Fin j) (Fin j) ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hNM : N * (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) = 1)
    (b : ℕ) (hb : b < j) (q : Fin (2 * r + k + 1)) (hq : r + k < q.val) :
    Vv y N b q = if (sg k r q).val = b then 1 else 0 := by sorry
