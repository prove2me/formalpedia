-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FD_card_places
-- name    : GlobalTheory.CompanionTheory.SW.FD.card_places
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:24:46.527649+00:00
-- url     : https://prove2.me/theorems/04f6a584-0e31-443b-86a9-36f60d578bec
-- title:
--   FD: card places
-- statement:
--   The FD construction uses the card places property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean#L53-L55

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

theorem GlobalTheory.CompanionTheory.SW.FD.card_places (hF : IsTotallyReal F) :
    Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by sorry
