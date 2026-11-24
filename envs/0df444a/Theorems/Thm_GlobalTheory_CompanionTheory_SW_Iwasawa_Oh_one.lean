-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Iwasawa_Oh_one
-- name    : GlobalTheory.CompanionTheory.SW.Iwasawa.Oh_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:07:00.576496+00:00
-- url     : https://prove2.me/theorems/aa4d43cf-5841-4ee4-80ab-943789a30c24
-- title:
--   Iwasawa: Oh one
-- statement:
--   The Iwasawa construction uses the Oh one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IwasawaDecompositionAdelicSL2.lean#L89-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/IwasawaDecompositionAdelicSL2.lean#L89-L89

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

theorem GlobalTheory.CompanionTheory.SW.Iwasawa.Oh_one : (1 : A F) ∈ Oh F := by sorry
