-- Prove2me | Theorems.Thm_GlobalTheory_T_partialFourierHermitianBlock_isLocallyConstant
-- name    : GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:58.952157+00:00
-- url     : https://prove2.me/theorems/bce78707-43f3-4c01-ba58-a75455daac1f
-- title:
--   T: partial Fourier Hermitian Block is Locally Constant
-- statement:
--   The T construction uses the partial Fourier Hermitian Block is Locally Constant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierHermitianBlockIsLocallyConstantStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PartialFourierHermitianBlockIsLocallyConstantStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockIsLocallyConstant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PartialFourierHermitianBlockIsLocallyConstantStatement
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

theorem GlobalTheory.T.partialFourierHermitianBlock_isLocallyConstant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → IsLocallyConstant (fourU M ψ f) := by sorry
