-- Prove2me | Theorems.Thm_GlobalTheory_levelTheta_zero_zero_mem
-- name    : GlobalTheory.levelTheta_zero_zero_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:36:23.805004+00:00
-- url     : https://prove2.me/theorems/400e1a33-0820-500b-82d4-cf5ff7a16eec
-- title:
--   Global Theory: level Theta zero zero mem
-- statement:
--   The Global Theory construction uses the level Theta zero zero mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean#L346-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/EqZeroOfSemicharacterMultiplier.lean#L346-L348

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ContinuousRl
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.PTheta
open GlobalTheory
variable {ι : Type} [Fintype ι]
variable {N M : ℕ} {τ : Matrix ι ι ℂ} {a b : ι → ℝ} {f g : (ι → ℂ) → ℂ}

theorem GlobalTheory.levelTheta_zero_zero_mem (hτ : τ ∈ SiegelH ι) (hN : 0 < N) (c : ι → ℤ) :
    levelTheta 0 0 N τ c ∈ thetaLevel N τ := by sorry
