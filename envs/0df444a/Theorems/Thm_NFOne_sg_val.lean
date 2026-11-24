-- Prove2me | Theorems.Thm_NFOne_sg_val
-- name    : NFOne.sg_val
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T15:06:27.550902+00:00
-- url     : https://prove2.me/theorems/746e4edc-a90d-4f22-b7c9-4a89d437a22b
-- title:
--   NFOne: sg val
-- statement:
--   The NFOne construction uses the sg val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L11-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L11-L11

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

theorem NFOne.sg_val (k r : ℕ) (i : Fin (2 * r + k + 1)) : (sg k r i).val = 2 * r + k - i.val := by sorry

attribute [defeq] NFOne.sg_val
