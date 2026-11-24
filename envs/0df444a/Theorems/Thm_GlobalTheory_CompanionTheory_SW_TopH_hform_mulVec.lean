-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TopH_hform_mulVec
-- name    : GlobalTheory.CompanionTheory.SW.TopH.hform_mulVec
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:11:14.265392+00:00
-- url     : https://prove2.me/theorems/dc1adce6-2b67-4e2b-9d13-72b3ba9cb67a
-- title:
--   Top H: hform mul Vec
-- statement:
--   The Top H construction uses the hform mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupLocallyCompact.lean#L12-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupLocallyCompact.lean#L12-L25

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TopH
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.TopH.hform_mulVec {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J g : Matrix (Fin m) (Fin m) A)
    (hg : cT σ g * J * g = J) (x y : Fin m → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by sorry
