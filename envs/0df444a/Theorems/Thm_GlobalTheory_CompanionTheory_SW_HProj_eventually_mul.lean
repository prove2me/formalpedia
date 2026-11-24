-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_eventually_mul
-- name    : GlobalTheory.CompanionTheory.SW.HProj.eventually_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:04:48.15349+00:00
-- url     : https://prove2.me/theorems/bfaa3dfc-27a5-4d1d-b722-ccc6f356956e
-- title:
--   HProj: eventually mul
-- statement:
--   The HProj construction uses the eventually mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L134-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L134-L155

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
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem GlobalTheory.CompanionTheory.SW.HProj.eventually_mul (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ y z : Fv F v ⊗[F] E, y ∈ Lv b v → z ∈ Lv b v → y * z ∈ Lv b v := by sorry
