-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DualLattice_exists_dual_param
-- name    : GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:11:59.615608+00:00
-- url     : https://prove2.me/theorems/79339280-2c0f-498a-8deb-d6eef4020fc6
-- title:
--   Dual Lattice: exists dual param
-- statement:
--   The Dual Lattice construction uses the exists dual param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrization.lean#L40-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrization.lean#L40-L79

import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DualLatticeParametrization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW GlobalTheory.CompanionTheory.SW.ThW.DualLattice

theorem GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_dual_param (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    [DecidableEq ι] (B : Matrix ι ι F) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ)
    (hB : B.det ≠ 0) (hN : 0 < N) :
    ∃ e : (ι × InfinitePlace F → ℤ) → ι → F,
      (∀ n i v, (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ e n) i) = n (i, v)) ∧
      ∀ y : ι → F, (∀ i v, ∃ m : ℤ,
        (N : ℚ) * Algebra.trace ℚ F ((b v : F) * (B *ᵥ y) i) = m) → ∃ n, e n = y := by sorry
