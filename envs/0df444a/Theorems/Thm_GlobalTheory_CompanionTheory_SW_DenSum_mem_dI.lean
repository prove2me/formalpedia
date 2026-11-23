-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_DenSum_mem_dI
-- name    : GlobalTheory.CompanionTheory.SW.DenSum.mem_dI
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:59:59.311853+00:00
-- url     : https://prove2.me/theorems/593da876-a38d-4bf2-9d07-d660d3887eda
-- title:
--   Den Sum: mem d I
-- statement:
--   The Den Sum construction uses the mem d I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DenominatorPowerSummable.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DenominatorPowerSummable.lean#L15-L17

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CountableIdealSummableAbsNormRpow
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DenominatorPowerSummable
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DenSum
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.DenSum.mem_dI {b : F} {x : 𝓞 F} : x ∈ dI b ↔ ∃ t : 𝓞 F, (t : F) = (x : F) * b := by sorry
