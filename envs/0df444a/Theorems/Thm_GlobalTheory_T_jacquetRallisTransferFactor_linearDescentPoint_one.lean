-- Prove2me | Theorems.Thm_GlobalTheory_T_jacquetRallisTransferFactor_linearDescentPoint_one
-- name    : GlobalTheory.T.jacquetRallisTransferFactor_linearDescentPoint_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:40.31853+00:00
-- url     : https://prove2.me/theorems/a2b8b5d8-feca-57f7-8e61-1d8b7c413de1
-- title:
--   T: jacquet Rallis Transfer Factor linear Descent Point one
-- statement:
--   The T construction uses the jacquet Rallis Transfer Factor linear Descent Point one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorLinearDescentPointOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorLinearDescentPointOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorLinearDescentPointOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorLinearDescentPointOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.jacquetRallisTransferFactor_linearDescentPoint_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∃ κ₀ : ℂ, ∀ a : A.K, IsUnit a → ∀ g : GL (Fin r) F, omega (act g (LinDesc.pt A hG lam 1 a)) = κ₀ * eta ((g : Matrix (Fin r) (Fin r) F).det) * A.etaK a := by sorry
