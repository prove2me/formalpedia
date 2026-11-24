-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_eq_of_cosets
-- name    : GlobalTheory.CompanionTheory.SW.Core.Density.eq_of_cosets
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:03:03.379804+00:00
-- url     : https://prove2.me/theorems/ca71fc72-b2f7-4017-a35d-b19fe46fbc1f
-- title:
--   Density: eq of cosets
-- statement:
--   The Density construction uses the eq of cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L177-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L177-L248

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhatStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_PositiveDefiniteDensity
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Density
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
variable [IsTopologicalAddGroup V] [T2Space V] [SecondCountableTopology V] [BorelSpace V]

theorem GlobalTheory.CompanionTheory.SW.Core.Density.eq_of_cosets {m m' : Measure V} [IsFiniteMeasure m]
    (hb : ∀ U ∈ 𝓝 (0 : V), ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
      (L : Set V) ⊆ U)
    (hcov : ∀ x : V, ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ x ∈ L)
    (heq : ∀ (L : AddSubgroup V) (a : V), IsCompact (L : Set V) → IsOpen (L : Set V) →
      m (coset L a) = m' (coset L a)) : m = m' := by sorry
