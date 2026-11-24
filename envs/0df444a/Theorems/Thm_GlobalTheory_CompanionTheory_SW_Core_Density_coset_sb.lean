-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_Density_coset_sb
-- name    : GlobalTheory.CompanionTheory.SW.Core.Density.coset_sb
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:02:58.503982+00:00
-- url     : https://prove2.me/theorems/9c7a37cb-12ac-4ad5-928f-dba93c2c1511
-- title:
--   Density: coset sb
-- statement:
--   The Density construction uses the coset sb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/PositiveDefiniteDensity.lean#L66-L71

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
variable [IsTopologicalAddGroup V]

theorem GlobalTheory.CompanionTheory.SW.Core.Density.coset_sb [T2Space V] {L : AddSubgroup V} (hK : IsCompact (L : Set V)) (hO : IsOpen (L : Set V))
    (a : V) : SB (Set.indicator (coset L a) (fun _ => (1 : ℂ))) := by sorry
