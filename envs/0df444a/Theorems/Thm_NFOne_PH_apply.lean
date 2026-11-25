-- Prove2me | Theorems.Thm_NFOne_PH_apply
-- name    : NFOne.PH_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:53:18.981993+00:00
-- url     : https://prove2.me/theorems/eb6db8f4-2a47-4668-89a0-bd8c76b5dcce
-- title:
--   NFOne: PH apply
-- statement:
--   The NFOne construction uses the PH apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/PRowWSColW.lean#L103-L111

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

theorem NFOne.PH_apply (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ) (p q : Fin (2 * r + k + 1)) :
    ((Pm k r j V)ᴴ * Hpk k r) p q = if r ≤ q.val ∧ q.val ≤ r + k then dW k r q * star (Pm k r j V q p)
      else star (Pm k r j V (sg k r q) p) := by sorry
