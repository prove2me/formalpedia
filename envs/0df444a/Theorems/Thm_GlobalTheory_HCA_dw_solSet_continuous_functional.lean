-- Prove2me | Theorems.Thm_GlobalTheory_HCA_dw_solSet_continuous_functional
-- name    : GlobalTheory.HCA.dw_solSet_continuous_functional
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:59:47.11882+00:00
-- url     : https://prove2.me/theorems/ad0eabd4-ff9a-4cac-8569-6ea500399ad5
-- title:
--   HCA: dw sol Set continuous functional
-- statement:
--   The HCA construction uses the dw sol Set continuous functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticSystemDerivativeContinuousFunctional.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticSystemDerivativeContinuousFunctional.lean#L40-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory.HCA.SolFunc

theorem GlobalTheory.HCA.dw_solSet_continuous_functional : ∀ (d : ℕ) (ι : Type) [Fintype ι] (P : Sys d ι) (U : Set (E d)), IsOpen U → (∀ i n w, ContDiffOn ℝ ∞ (P.a i n w) U) → (∀ x ∈ U, ∀ ξ : E d, ξ ≠ 0 → ∃ i, P.symb i x ξ ≠ 0) → ∀ S : Submodule ℂ (U →ᵇ ℂ), (S : Set (U →ᵇ ℂ)) = solSet P U → ∀ (w : List (Fin d)), ∀ x ∈ U, ∃ l : S →L[ℂ] ℂ, ∀ u : S, l u = dw w (ext0 U (u : U →ᵇ ℂ)) x := by sorry
