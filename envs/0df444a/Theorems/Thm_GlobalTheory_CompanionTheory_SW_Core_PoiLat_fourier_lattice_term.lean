-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_PoiLat_fourier_lattice_term
-- name    : GlobalTheory.CompanionTheory.SW.Core.PoiLat.fourier_lattice_term
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:04:10.927971+00:00
-- url     : https://prove2.me/theorems/1f863027-ee69-4863-aa29-abd69d5be7cb
-- title:
--   Poi Lat: fourier lattice term
-- statement:
--   The Poi Lat construction uses the fourier lattice term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PoissonSummationGaussian.lean#L84-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PoissonSummationGaussian.lean#L84-L100

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PoissonSummationGaussian
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.PoiLat
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem GlobalTheory.CompanionTheory.SW.Core.PoiLat.fourier_lattice_term {Z : Matrix κ κ ℂ} (hZ : GlobalTheory.IsSiegel Z) {g : Matrix κ κ ℝ}
    (hg : g.det ≠ 0) (n : κ → ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I) *
        ((fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)) ⬝ᵥ
          (Z⁻¹ *ᵥ fun i => ((((g⁻¹)ᵀ *ᵥ fun i => (n i : ℝ)) i : ℝ) : ℂ)))) =
      GlobalTheory.riemannThetaTerm 0 0 (-((g.map Complex.ofReal)ᵀ * Z * g.map Complex.ofReal)⁻¹) 0 n := by sorry
