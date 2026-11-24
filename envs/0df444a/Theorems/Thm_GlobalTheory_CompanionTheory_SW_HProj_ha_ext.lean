-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_ha_ext
-- name    : GlobalTheory.CompanionTheory.SW.HProj.ha_ext
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:05:11.921421+00:00
-- url     : https://prove2.me/theorems/0e27dadd-f967-41fc-9852-b2a68c6064f6
-- title:
--   HProj: ha ext
-- statement:
--   The HProj construction uses the ha ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L81-L84

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F : Type} (E : Type) [Field F] [Field E] [Algebra F E]
  {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R''] [Algebra F R'']
variable {E}

theorem GlobalTheory.CompanionTheory.SW.HProj.ha_ext (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {g h : HA R σ J}
    (e : ((HA.mat R σ J g : GL _ _) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = (HA.mat R σ J h : GL _ _)) :
    g = h := by sorry
