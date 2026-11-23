-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hE_conj
-- name    : GlobalTheory.CompanionTheory.SW.HypSplit.hE_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:11.992796+00:00
-- url     : https://prove2.me/theorems/e542c373-fcff-4f51-aaf7-de57b0e7df04
-- title:
--   Hyp Split: h E conj
-- statement:
--   The Hyp Split construction uses the h E conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean#L30-L35

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

theorem GlobalTheory.CompanionTheory.SW.HypSplit.hE_conj (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (u v : Fin M → E) :
    σ (hE σ J u v) = hE σ J v u := by sorry
