-- Prove2me | Theorems.Thm_NFOne_HP_apply
-- name    : NFOne.HP_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:37:51.760112+00:00
-- url     : https://prove2.me/theorems/42415269-df1a-4281-89fe-a0ef37cc0d42
-- title:
--   NFOne: HP apply
-- statement:
--   The NFOne construction uses the HP apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L97-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L97-L101

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

theorem NFOne.HP_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    (Hpk k r * Pm k r j V) p q = if r ≤ p.val ∧ p.val ≤ r + k then dW k r p * Pm k r j V p q
      else Pm k r j V (sg k r p) q := by sorry
