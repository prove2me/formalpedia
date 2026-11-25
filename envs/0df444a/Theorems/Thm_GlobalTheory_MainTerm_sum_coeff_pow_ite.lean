-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_sum_coeff_pow_ite
-- name    : GlobalTheory.MainTerm.sum_coeff_pow_ite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:53:54.323084+00:00
-- url     : https://prove2.me/theorems/6536f99a-5867-48a6-a72e-bb4f7c4a8e3c
-- title:
--   Main Term: sum coeff pow ite
-- statement:
--   The Main Term construction uses the sum coeff pow ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSq.lean#L39-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/CoeffCoordinatesGoodTangentsLtSq.lean#L39-L49

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasisStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffCoordinatesGoodTangentsLtSq
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem GlobalTheory.MainTerm.sum_coeff_pow_ite {C : Type} [Field C] {I : Type} [Fintype I] {N : ℕ} (em : Fin N ↪ I)
    (g : I → C) {n : ℕ} (hn : n ≠ 0) (μ : Fin N →₀ ℕ) :
    ∑ c, g c * MvPowerSeries.coeff μ
        ((∑ δ : Fin N, if em δ = c then (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) else 0) ^ n) =
      ∑ δ : Fin N, g (em δ) * MvPowerSeries.coeff μ ((MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ n) := by sorry
