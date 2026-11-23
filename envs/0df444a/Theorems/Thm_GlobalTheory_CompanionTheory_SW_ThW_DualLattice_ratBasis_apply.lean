-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_DualLattice_ratBasis_apply
-- name    : GlobalTheory.CompanionTheory.SW.ThW.DualLattice.ratBasis_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:52.404358+00:00
-- url     : https://prove2.me/theorems/da92086b-c569-41e5-bf6a-480bdb7954e7
-- title:
--   Dual Lattice: rat Basis apply
-- statement:
--   The Dual Lattice construction uses the rat Basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrization.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DualLatticeParametrization.lean#L11-L13

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

theorem GlobalTheory.CompanionTheory.SW.ThW.DualLattice.ratBasis_apply {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (b : Module.Basis κ ℤ (𝓞 F)) (v : κ) : ratBasis b v = (b v : F) := by sorry
