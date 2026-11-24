-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Core_RowCompletion_integral_inv_mul
-- name    : GlobalTheory.CompanionTheory.SW.Core.RowCompletion.integral_inv_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:04:12.403565+00:00
-- url     : https://prove2.me/theorems/db9676b9-4e2b-4f82-a943-4741379bf97d
-- title:
--   Row Completion: integral inv mul
-- statement:
--   The Row Completion construction uses the integral inv mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CuspRepresentativesFinite.lean#L56-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/CuspRepresentativesFinite.lean#L56-L91

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CuspRepresentativesFinite
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.RowCompletion
open nonZeroDivisors
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.SW.Core.RowCompletion.integral_inv_mul {A : FractionalIdeal (𝓞 F)⁰ F} (hA : A ≠ 0) {r g : SL(2, F)}
    (hr : Adapted A r) (hg : Adapted A g) (i j : Fin 2) :
    ∃ z : 𝓞 F, (z : F) = (r⁻¹ * g) i j := by sorry
