-- Prove2me | Theorems.Thm_GlobalTheory_T_psiK_mul_NL_eq_one_on_integral_lattice
-- name    : GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:54:55.905128+00:00
-- url     : https://prove2.me/theorems/fe7845ee-d96a-4ad4-8685-d6fadd5e0dbb
-- title:
--   T: psi K mul NL eq one on integral lattice
-- statement:
--   The T construction uses the psi K mul NL eq one on integral lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PsiKMulNLEqOneOnIntegralLatticeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/PsiKMulNLEqOneOnIntegralLatticeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PsiKMulNLEqOneOnIntegralLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PsiKMulNLEqOneOnIntegralLatticeStatement
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

theorem GlobalTheory.T.psiK_mul_NL_eq_one_on_integral_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.K) (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ y : A.L, (∀ i, ‖j y i‖ ≤ 1) → A.psiK ψ (x * A.NL y) = 1 := by sorry
