-- Prove2me | Theorems.Thm_NFOne_Hpk_symm
-- name    : NFOne.Hpk_symm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:07.466437+00:00
-- url     : https://prove2.me/theorems/c40b0e60-8f82-43be-ac04-4e8e0cf644a1
-- title:
--   NFOne: Hpk symm
-- statement:
--   The NFOne construction uses the Hpk symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L33-L37

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

theorem NFOne.Hpk_symm (k r : ℕ) (p l : Fin (2 * r + k + 1)) : Hpk k r p l = Hpk k r l p := by sorry
