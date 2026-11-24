-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_blockGL_injective
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.blockGL_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:10:46.202111+00:00
-- url     : https://prove2.me/theorems/b1020f18-7ce6-46a1-a140-dcc706f679e7
-- title:
--   Stab First: block GL injective
-- statement:
--   The Stab First construction uses the block GL injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L61-L66

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}

theorem GlobalTheory.CompanionTheory.SW.StabFirst.blockGL_injective : Function.Injective (blockGL : GL (Fin M) K → GL (Fin (M + 1)) K) := by sorry
