-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_exists_value_eq_zpow
-- name    : GlobalTheory.CompanionTheory.UnramDict.exists_value_eq_zpow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:21:59.423368+00:00
-- url     : https://prove2.me/theorems/e8074c16-8f71-4869-ad98-5233da7cdb63
-- title:
--   Unram Dict: exists value eq zpow
-- statement:
--   The Unram Dict construction uses the exists value eq zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L25-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L25-L55

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_Development
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnramifiedExtensionIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Topology Filter
open PositivityTheory.Rg.Tf.Loc
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnramDict
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}

theorem GlobalTheory.CompanionTheory.UnramDict.exists_value_eq_zpow {π : K} (h0 : valuation K π ≠ 0) (h1 : valuation K π < 1)
    (hmax : ∀ x : K, valuation K x < 1 → valuation K x ≤ valuation K π) {x : K} (hx : x ≠ 0) :
    ∃ m : ℤ, valuation K x = valuation K π ^ m := by sorry
