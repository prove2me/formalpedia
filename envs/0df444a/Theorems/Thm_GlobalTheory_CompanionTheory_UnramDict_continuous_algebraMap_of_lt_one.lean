-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_continuous_algebraMap_of_lt_one
-- name    : GlobalTheory.CompanionTheory.UnramDict.continuous_algebraMap_of_lt_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:19:55.826225+00:00
-- url     : https://prove2.me/theorems/de7c0948-11dc-470f-8b49-d3a8a78b5732
-- title:
--   Unram Dict: continuous algebra Map of lt one
-- statement:
--   The Unram Dict construction uses the continuous algebra Map of lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L107-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L107-L126

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
variable {k E : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra k E]

theorem GlobalTheory.CompanionTheory.UnramDict.continuous_algebraMap_of_lt_one [ValuativeExtension k E] {π : k}
    (h0 : valuation E (algebraMap k E π) ≠ 0) (h1 : valuation E (algebraMap k E π) < 1) :
    Continuous (algebraMap k E) := by sorry
