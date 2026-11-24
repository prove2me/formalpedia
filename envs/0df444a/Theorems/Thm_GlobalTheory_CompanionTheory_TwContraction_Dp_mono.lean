-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_Dp_mono
-- name    : GlobalTheory.CompanionTheory.TwContraction.Dp.mono
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:22.247502+00:00
-- url     : https://prove2.me/theorems/75b14468-deb0-4a0f-91be-82fb56c3ace9
-- title:
--   Dp: mono
-- statement:
--   The Dp construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L29-L31

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IwahoriFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TwistedIwahoriContractionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Tf.Loc Matrix ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TwContraction
variable {F : Type*} [Field F] [ValuativeRel F] {n : ℕ}

theorem GlobalTheory.CompanionTheory.TwContraction.Dp.mono {ρ : ValueGroupWithZero F} (hρ : ρ ≤ 1) {a b : ℕ} (hab : a ≤ b)
    {M : Matrix (Fin n) (Fin n) F} (hM : Dp ρ b M) : Dp ρ a M := by sorry
