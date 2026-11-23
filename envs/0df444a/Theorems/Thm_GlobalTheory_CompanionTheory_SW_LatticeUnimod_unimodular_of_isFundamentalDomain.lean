-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LatticeUnimod_unimodular_of_isFundamentalDomain
-- name    : GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:29:35.306414+00:00
-- url     : https://prove2.me/theorems/f77c1a75-86f6-4c36-8016-ba05dac724dd
-- title:
--   Lattice Unimod: unimodular of is Fundamental Domain
-- statement:
--   The Lattice Unimod construction uses the unimodular of is Fundamental Domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteCovolumeUnimodular.lean#L8-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FiniteCovolumeUnimodular.lean#L8-L52

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FiniteCovolumeUnimodular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LatticeUnimod

theorem GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
      [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
      (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G),
      IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤ →
        μ 𝓕 ≠ 0 ∧ μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by sorry
