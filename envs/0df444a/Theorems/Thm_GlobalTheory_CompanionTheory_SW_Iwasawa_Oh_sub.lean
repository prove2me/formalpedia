-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_Oh_sub
-- name    : GlobalTheory.CompanionTheory.SW.Iwasawa.Oh_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:06:55.074787+00:00
-- url     : https://prove2.me/theorems/95ec7167-a28b-41a2-a4e8-0481f46bf7fc
-- title:
--   Iwasawa: Oh sub
-- statement:
--   The Iwasawa construction uses the Oh sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IwasawaDecompositionAdelicSL2.lean#L94-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IwasawaDecompositionAdelicSL2.lean#L94-L95

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IwasawaDecompositionAdelicSL2
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Iwasawa
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.Iwasawa.Oh_sub {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x - y ∈ Oh F := by sorry
