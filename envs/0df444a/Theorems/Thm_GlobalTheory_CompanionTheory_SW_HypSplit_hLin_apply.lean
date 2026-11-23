-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HypSplit_hLin_apply
-- name    : GlobalTheory.CompanionTheory.SW.HypSplit.hLin_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:56.357975+00:00
-- url     : https://prove2.me/theorems/b0e22cae-9cfc-4736-b424-ff29117d46b5
-- title:
--   Hyp Split: h Lin apply
-- statement:
--   The Hyp Split construction uses the h Lin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IsotropicVectorSplitsHyperbolicPlane.lean#L26-L26

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

theorem GlobalTheory.CompanionTheory.SW.HypSplit.hLin_apply (u v : Fin M → E) : hLin σ J u v = hE σ J u v := by sorry

attribute [defeq] GlobalTheory.CompanionTheory.SW.HypSplit.hLin_apply
