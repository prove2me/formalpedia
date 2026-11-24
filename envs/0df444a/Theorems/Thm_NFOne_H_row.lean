-- Prove2me | Theorems.Thm_NFOne_H_row
-- name    : NFOne.H_row
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:07:50.632927+00:00
-- url     : https://prove2.me/theorems/433e3708-06c2-42d8-a09d-71144338acec
-- title:
--   NFOne: H row
-- statement:
--   The NFOne construction uses the H row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L39-L44

import Definitions.Def_Formalism_HermitianCurvature_OperatorsCommuteTranslations
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Formalism.QuantumDeterminants
noncomputable section
open NFOne

theorem NFOne.H_row (k r : ℕ) (p : Fin (2 * r + k + 1)) (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ l, Hpk k r p l * f l =
      if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * f p else f (sg k r p) := by sorry
