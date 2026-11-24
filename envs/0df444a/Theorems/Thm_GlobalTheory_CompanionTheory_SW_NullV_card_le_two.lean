-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_NullV_card_le_two
-- name    : GlobalTheory.CompanionTheory.SW.NullV.card_le_two
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:21:11.196127+00:00
-- url     : https://prove2.me/theorems/511f3824-b313-45b9-88f9-a48407da6437
-- title:
--   Null V: card le two
-- statement:
--   The Null V construction uses the card le two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HaarMeasureNonunitsNull.lean#L76-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HaarMeasureNonunitsNull.lean#L76-L89

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianNondegRepresentsNonzeroScalar
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HaarMeasureNonunitsNull
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
noncomputable section
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NullV

theorem GlobalTheory.CompanionTheory.SW.NullV.card_le_two {K : Type} [Field K] (a b q : K) (hq : q ≠ 0) (r : ℕ → K)
    (hr : Function.Injective r) (s : Finset ℕ)
    (h : ∀ i ∈ s, a + r i * b + r i ^ 2 * q = 0) : s.card ≤ 2 := by sorry
