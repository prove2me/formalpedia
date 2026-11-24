-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TwContraction_continuous_map_gl
-- name    : GlobalTheory.CompanionTheory.TwContraction.continuous_map_gl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:18:11.742922+00:00
-- url     : https://prove2.me/theorems/3805a7a9-734a-4605-8b1b-2aa3ae37ffb3
-- title:
--   Tw Contraction: continuous map gl
-- statement:
--   The Tw Contraction construction uses the continuous map gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L363-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TwistedIwahoriContractionHolds.lean#L363-L372

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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GlobalTheory.CompanionTheory.TwContraction.continuous_map_gl (φ : F →+* F) (hφ : Continuous φ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) φ) := by sorry
