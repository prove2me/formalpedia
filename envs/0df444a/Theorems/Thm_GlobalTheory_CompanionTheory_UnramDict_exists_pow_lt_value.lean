-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnramDict_exists_pow_lt_value
-- name    : GlobalTheory.CompanionTheory.UnramDict.exists_pow_lt_value
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:09.144677+00:00
-- url     : https://prove2.me/theorems/4e6fe136-8124-4701-915d-4164e7810138
-- title:
--   Unram Dict: exists pow lt value
-- statement:
--   The Unram Dict construction uses the exists pow lt value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnramifiedExtensionIntegralBasis.lean#L17-L21

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

theorem GlobalTheory.CompanionTheory.UnramDict.exists_pow_lt_value {a γ : ValueGroupWithZero K} (ha : a < 1) (hγ : γ ≠ 0) :
    ∃ m : ℕ, a ^ m < γ := by sorry
