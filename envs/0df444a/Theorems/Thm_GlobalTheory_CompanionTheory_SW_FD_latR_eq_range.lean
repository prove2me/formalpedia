-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_latR_eq_range
-- name    : GlobalTheory.CompanionTheory.SW.FD.latR_eq_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:14.39328+00:00
-- url     : https://prove2.me/theorems/df7c73be-739c-4d00-a072-316d6db3f362
-- title:
--   FD: lat R eq range
-- statement:
--   The FD construction uses the lat R eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L18-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L18-L28

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.FD.latR_eq_range (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) :
    latR ρ N = (scaleMap ρ N).range := by sorry
