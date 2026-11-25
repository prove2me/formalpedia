-- Prove2me | Theorems.Thm_NFOne_PHP_apply
-- name    : NFOne.PHP_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:16.86824+00:00
-- url     : https://prove2.me/theorems/dfb1b9a1-389f-4634-8e55-dc5ce194b3f1
-- title:
--   NFOne: PHP apply
-- statement:
--   The NFOne construction uses the PHP apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L113-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L113-L126

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

theorem NFOne.PHP_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * (Hpk k r * Pm k r j V)) p q = ∑ i, (if r ≤ i.val ∧ i.val ≤ r + k then
      dW k r i * star (Pm k r j V i p) * Pm k r j V i q else 0) := by sorry
