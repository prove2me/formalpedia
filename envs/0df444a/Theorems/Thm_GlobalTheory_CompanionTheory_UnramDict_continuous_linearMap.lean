-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_continuous_linearMap
-- name    : GlobalTheory.CompanionTheory.UnramDict.continuous_linearMap
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:20:13.309804+00:00
-- url     : https://prove2.me/theorems/d0eaf65b-ac87-42df-9dfa-e4768ce4a337
-- title:
--   Unram Dict: continuous linear Map
-- statement:
--   The Unram Dict construction uses the continuous linear Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L128-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L128-L138

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

theorem GlobalTheory.CompanionTheory.UnramDict.continuous_linearMap [FiniteDimensional k E] [ContinuousSMul k E] (f : E →ₗ[k] E) :
    Continuous f := by sorry
