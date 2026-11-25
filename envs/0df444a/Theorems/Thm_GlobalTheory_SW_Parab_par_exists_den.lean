-- Prove2me | Theorems.Thm_GlobalTheory_SW_Parab_par_exists_den
-- name    : GlobalTheory.SW.Parab.par_exists_den
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:21:36.08187+00:00
-- url     : https://prove2.me/theorems/fdef7d17-b530-4029-90da-4269c520f3e2
-- title:
--   Parab: par exists den
-- statement:
--   The Parab construction uses the par exists den property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/SiegelThetaTransformationSiegelParabolic.lean#L11-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab

theorem GlobalTheory.SW.Parab.par_exists_den {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) :
    ∃ N : ℕ, 0 < N ∧ ∀ i j, IsIntegral ℤ (((N : ℚ) • S) i j) := by sorry
