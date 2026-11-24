-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Dens_prod_integrable
-- name    : GlobalTheory.CompanionTheory.SW.Core.Dens.prod_integrable
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:51.946995+00:00
-- url     : https://prove2.me/theorems/a0503d1c-d330-43c5-b4f8-6082c1f95133
-- title:
--   Dens: prod integrable
-- statement:
--   The Dens construction uses the prod integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuadraticLevelSetDensity.lean#L71-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/QuadraticLevelSetDensity.lean#L71-L76

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourierStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticLevelSetDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Dens
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.SW.Core.Dens.prod_integrable (M : ℕ) (hM : 3 ≤ M) :
    Integrable (fun x : InfinitePlace F → ℝ => (∏ w, ‖(x w : ℂ) + Complex.I‖ ^ M)⁻¹) := by sorry
