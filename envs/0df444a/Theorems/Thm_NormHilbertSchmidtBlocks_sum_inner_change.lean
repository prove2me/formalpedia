-- Prove2me | Theorems.Thm_NormHilbertSchmidtBlocks_sum_inner_change
-- name    : NormHilbertSchmidtBlocks.sum_inner_change
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:52:41.820699+00:00
-- url     : https://prove2.me/theorems/e0084c82-f6e1-44af-920a-101d52802cd2
-- title:
--   Norm Hilbert Schmidt Blocks: sum inner change
-- statement:
--   The Norm Hilbert Schmidt Blocks construction uses the sum inner change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HilbertSchmidtBlocks/Change.lean#L10-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HilbertSchmidtBlocks/Change.lean#L10-L29

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_Change
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open NormHilbertSchmidtBlocks

theorem NormHilbertSchmidtBlocks.sum_inner_change {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (e : κ → E)
    (he : ∀ x y : E, ∑ k, inner ℂ x (e k) * inner ℂ (e k) y = inner ℂ x y)
    (A B : E →ₗ[ℂ] F) :
    ∑ k, inner ℂ (A (e k)) (B (e k)) = ∑ i, inner ℂ (A (b i)) (B (b i)) := by sorry
