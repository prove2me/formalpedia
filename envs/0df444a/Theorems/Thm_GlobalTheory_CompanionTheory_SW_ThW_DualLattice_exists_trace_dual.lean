-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DualLattice_exists_trace_dual
-- name    : GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_trace_dual
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:10:51.823474+00:00
-- url     : https://prove2.me/theorems/f42fca77-4ec7-4ec6-99d6-ad4d2743eefa
-- title:
--   Dual Lattice: exists trace dual
-- statement:
--   The Dual Lattice construction uses the exists trace dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrization.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrization.lean#L15-L24

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

theorem GlobalTheory.CompanionTheory.SW.ThW.DualLattice.exists_trace_dual {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    [DecidableEq κ] (b : Module.Basis κ ℤ (𝓞 F)) :
    ∃ d : κ → F, ∀ v u, Algebra.trace ℚ F ((b v : F) * d u) = if v = u then 1 else 0 := by sorry
