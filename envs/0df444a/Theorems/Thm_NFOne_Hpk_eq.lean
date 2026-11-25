-- Prove2me | Theorems.Thm_NFOne_Hpk_eq
-- name    : NFOne.Hpk_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:52:24.517465+00:00
-- url     : https://prove2.me/theorems/b14a9d1e-2f17-4ede-a035-9b1e7b87f923
-- title:
--   NFOne: Hpk eq
-- statement:
--   The NFOne construction uses the Hpk eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L25-L31

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

theorem NFOne.Hpk_eq (k r : ℕ) (p l : Fin (2 * r + k + 1)) :
    Hpk k r p l = if r ≤ p.val ∧ p.val ≤ r + k then (if l = p then dW k r p else 0)
      else (if l = sg k r p then 1 else 0) := by sorry
