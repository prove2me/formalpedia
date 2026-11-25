-- Prove2me | Theorems.Thm_NFOne_sg_sg
-- name    : NFOne.sg_sg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:34.493133+00:00
-- url     : https://prove2.me/theorems/665a0ced-4da6-4436-81a9-a11a78c4f742
-- title:
--   NFOne: sg sg
-- statement:
--   The NFOne construction uses the sg sg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L13-L17

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

theorem NFOne.sg_sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by sorry
