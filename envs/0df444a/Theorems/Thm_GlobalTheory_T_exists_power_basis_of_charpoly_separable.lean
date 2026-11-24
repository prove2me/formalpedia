-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_power_basis_of_charpoly_separable
-- name    : GlobalTheory.T.exists_power_basis_of_charpoly_separable
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:38:25.280747+00:00
-- url     : https://prove2.me/theorems/ce6805a3-3587-48d3-8086-83d61dc8303a
-- title:
--   T: exists power basis of charpoly separable
-- statement:
--   The T construction uses the exists power basis of charpoly separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowerBasisOfCharpolySeparableStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPowerBasisOfCharpolySeparableStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPowerBasisOfCharpolySeparableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_power_basis_of_charpoly_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∃ e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A, ∀ i, e i = B.g ^ (i : ℕ) := by sorry
