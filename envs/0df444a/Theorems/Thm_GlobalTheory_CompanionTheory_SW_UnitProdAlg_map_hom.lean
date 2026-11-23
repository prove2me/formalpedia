-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_UnitProdAlg_map_hom
-- name    : GlobalTheory.CompanionTheory.SW.UnitProdAlg.map_hom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:43.117512+00:00
-- url     : https://prove2.me/theorems/b1c0fae2-2fbb-4bd8-971f-2bf6006f6586
-- title:
--   Unit Prod Alg: map hom
-- statement:
--   The Unit Prod Alg construction uses the map hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L19-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitProductClosureProperties.lean#L19-L30

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitProductClosureProperties
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.UnitProdAlg
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.UnitProdAlg.map_hom (f : ℝ≥0 →* ℝ≥0) {a : ℝ≥0} {c : HeightOneSpectrum (𝓞 F) → ℝ≥0}
    (h : IsUnitProd a c) : IsUnitProd (f a) (fun v => f (c v)) := by sorry
