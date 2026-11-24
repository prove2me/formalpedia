-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_tm_comp
-- name    : GlobalTheory.CompanionTheory.SW.HProj.tm_comp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:05:12.66344+00:00
-- url     : https://prove2.me/theorems/6b4727ba-652b-4fce-8a08-fdab216551d5
-- title:
--   HProj: tm comp
-- statement:
--   The HProj construction uses the tm comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L19-L24

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

theorem GlobalTheory.CompanionTheory.SW.HProj.tm_comp (φ : R →ₐ[F] R') (ψ : R' →ₐ[F] R'') (x : R ⊗[F] E) :
    tm E (ψ.comp φ) x = tm E ψ (tm E φ x) := by sorry
