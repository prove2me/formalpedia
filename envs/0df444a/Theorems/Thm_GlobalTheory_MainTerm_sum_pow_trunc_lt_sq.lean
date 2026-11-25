-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_sum_pow_trunc_lt_sq
-- name    : GlobalTheory.MainTerm.sum_pow_trunc_lt_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:54:15.358701+00:00
-- url     : https://prove2.me/theorems/e2f50e83-3a09-4c45-ae9d-c817b9049197
-- title:
--   Main Term: sum pow trunc lt sq
-- statement:
--   The Main Term construction uses the sum pow trunc lt sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSq.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSq.lean#L16-L30

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open Formalism.BaseCaseIdentities (OrdGE)
noncomputable section
open GlobalTheory GlobalTheory.MainTerm

theorem GlobalTheory.MainTerm.sum_pow_trunc_lt_sq {C : Type} [Field C] {I ι : Type} [Fintype I] {l : ℕ} (hl : 2 ≤ l)
    (T : I → MvPowerSeries ι C) (hT : ∀ c, OrdGE 1 (T c)) (f : I → ℕ → C) (μ : ι →₀ ℕ)
    (hμ : μ.degree < l ^ 2) :
    ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, f c s * MvPowerSeries.coeff μ (T c ^ (l ^ s)) =
      ∑ c, f c 0 * MvPowerSeries.coeff μ (T c) + ∑ c, f c 1 * MvPowerSeries.coeff μ (T c ^ l) := by sorry
