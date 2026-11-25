-- Prove2me | Theorems.Thm_GlobalTheory_SW_exists_linearIndependent_prod_norm_le
-- name    : GlobalTheory.SW.exists_linearIndependent_prod_norm_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:06:11.728657+00:00
-- url     : https://prove2.me/theorems/ea8a7e98-ff01-4617-be7f-4fe3ba76ded1
-- title:
--   SW: exists linear Independent prod norm le
-- statement:
--   The SW construction uses the exists linear Independent prod norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L78-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsLinearIndependentOfRatIndependent.lean#L78-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsLinearIndependentOfRatIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW

theorem GlobalTheory.SW.exists_linearIndependent_prod_norm_le {E U V ι : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι] {N : ℕ}
    (hι : Fintype.card ι = Module.finrank ℚ E * N) (φ : U →ₗ[ℤ] V) (u : ι → U)
    (hu : LinearIndependent ℝ fun k => φ (u k)) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ (∀ i, w i ∈ Submodule.span ℤ (Set.range u)) ∧
      ∏ i, ‖φ (w i)‖ ^ Module.finrank ℚ E ≤
        (Fintype.card ι : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * √(gram ℝ fun k => φ (u k)).det := by sorry
