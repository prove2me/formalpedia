-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_value_algebraMap_le_iff
-- name    : GlobalTheory.CompanionTheory.UnramDict.value_algebraMap_le_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:26.251795+00:00
-- url     : https://prove2.me/theorems/4d3ac9b3-e8ee-4b82-be17-1153e0ea49cb
-- title:
--   Unram Dict: value algebra Map le iff
-- statement:
--   The Unram Dict construction uses the value algebra Map le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L91-L95

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

theorem GlobalTheory.CompanionTheory.UnramDict.value_algebraMap_le_iff [ValuativeExtension k E] (a b : k) :
    valuation E (algebraMap k E a) ≤ valuation E (algebraMap k E b) ↔
      valuation k a ≤ valuation k b := by sorry
