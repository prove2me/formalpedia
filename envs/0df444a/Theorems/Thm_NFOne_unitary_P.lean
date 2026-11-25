-- Prove2me | Theorems.Thm_NFOne_unitary_P
-- name    : NFOne.unitary_P
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:37:43.413925+00:00
-- url     : https://prove2.me/theorems/db6b4cc5-c6dd-412b-b258-be035e66ae5a
-- title:
--   NFOne: unitary P
-- statement:
--   The NFOne construction uses the unitary P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/UnitaryP.lean#L138-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/NormFormOneUnitary/UnitaryP.lean#L138-L155

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_PRowWSColW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormFormOneUnitary_UnitaryP
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

theorem NFOne.unitary_P (k r j : ℕ) (V : ℕ → Fin (2 * r + k + 1) → ℂ)
    (V0 : ∀ c, j ≤ c → V c = 0)
    (Vs : ∀ b, b < j → ∀ q : Fin (2 * r + k + 1), r + k < q.val →
      V b q = if (sg k r q).val = b then 1 else 0)
    (Viso : ∀ b c, b < j → c < j → herm (Hpk k r) (V b) (V c) = 0) :
    (1 + Pm k r j V)ᴴ * Hpk k r * (1 + Pm k r j V) = Hpk k r := by sorry
