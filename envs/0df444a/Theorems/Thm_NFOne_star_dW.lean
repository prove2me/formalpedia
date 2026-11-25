-- Prove2me | Theorems.Thm_NFOne_star_dW
-- name    : NFOne.star_dW
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:42.57285+00:00
-- url     : https://prove2.me/theorems/c3b891a6-2293-4e88-b381-c726eb299eea
-- title:
--   NFOne: star d W
-- statement:
--   The NFOne construction uses the star d W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L21-L23

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

theorem NFOne.star_dW (k r : ℕ) (i : Fin (2 * r + k + 1)) : star (dW k r i) = dW k r i := by sorry
