-- Prove2me | Theorems.Thm_NFOne_Hpk_mulVec
-- name    : NFOne.Hpk_mulVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:37:07.302797+00:00
-- url     : https://prove2.me/theorems/18e34c78-f4fa-4448-ba1d-6dd2679f0e1c
-- title:
--   NFOne: Hpk mul Vec
-- statement:
--   The NFOne construction uses the Hpk mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L46-L48

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

theorem NFOne.Hpk_mulVec (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * v p else v (sg k r p) := by sorry
