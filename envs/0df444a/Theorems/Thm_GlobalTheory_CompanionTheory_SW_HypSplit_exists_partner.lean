-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_exists_partner
-- name    : GlobalTheory.CompanionTheory.SW.HypSplit.exists_partner
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:06:59.617552+00:00
-- url     : https://prove2.me/theorems/6aa9afe7-d020-4c9d-a2af-ce3728108c68
-- title:
--   Hyp Split: exists partner
-- statement:
--   The Hyp Split construction uses the exists partner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean#L37-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean#L37-L69

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IsotropicVectorSplitsHyperbolicPlane
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HypSplit
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {σ J}

theorem GlobalTheory.CompanionTheory.SW.HypSplit.exists_partner (hσ : ∀ a, σ (σ a) = a) (hJ : IsHermND σ J) (h2 : (2 : E) ≠ 0)
    (x : Fin M → E) (hx : x ≠ 0) (hxx : hE σ J x x = 0) :
    ∃ y, hE σ J x y = 1 ∧ hE σ J y y = 0 := by sorry
