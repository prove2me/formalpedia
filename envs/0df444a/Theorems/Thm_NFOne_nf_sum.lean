-- Prove2me | Theorems.Thm_NFOne_nf_sum
-- name    : NFOne.nf_sum
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:25.787688+00:00
-- url     : https://prove2.me/theorems/60574dd2-0731-4f91-a38b-9a2890283849
-- title:
--   NFOne: nf sum
-- statement:
--   The NFOne construction uses the nf sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L105-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/HermitianOrthogonalProjectionVector.lean#L105-L174

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

theorem NFOne.nf_sum (k r j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ)
    (N : Matrix (Fin j) (Fin j) ℂ)
    (hy2 : ∀ (a : Fin j) (b : Fin r), j ≤ b.val → y a (esI k r b) = 0)
    (hMN : (Matrix.of fun a b : Fin j => y a (sR k r j hj b)) * N = 1)
    (a : Fin j) (p : Fin (2 * r + k + 1)) :
    (Pm k r j (Vv y N) *ᵥ (fun q => if r + k < q.val then y a q else 0)) p =
      if r + k < p.val then 0 else y a p := by sorry
