-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_colM_injective
-- name    : GlobalTheory.CompanionTheory.SW.GramAlg.colM_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:24.864416+00:00
-- url     : https://prove2.me/theorems/98cd39b8-530b-4fa2-8c19-2f4cc04f2eeb
-- title:
--   Gram Alg: col M injective
-- statement:
--   The Gram Alg construction uses the col M injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L15-L18

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {A : Type} [CommRing A] {M n : ℕ}

theorem GlobalTheory.CompanionTheory.SW.GramAlg.colM_injective : Function.Injective (colM : (Fin n → Fin M → A) → _) := by sorry
