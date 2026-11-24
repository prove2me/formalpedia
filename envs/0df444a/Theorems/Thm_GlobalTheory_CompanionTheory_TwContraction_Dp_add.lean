-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_Dp_add
-- name    : GlobalTheory.CompanionTheory.TwContraction.Dp.add
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:13.108314+00:00
-- url     : https://prove2.me/theorems/9ce5c9a1-8b70-4f6b-b1fa-b087773c7d61
-- title:
--   Dp: add
-- statement:
--   The Dp construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L25-L27

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

theorem GlobalTheory.CompanionTheory.TwContraction.Dp.add {ρ : ValueGroupWithZero F} {a : ℕ} {M N : Matrix (Fin n) (Fin n) F}
    (hM : Dp ρ a M) (hN : Dp ρ a N) : Dp ρ a (M + N) := by sorry
