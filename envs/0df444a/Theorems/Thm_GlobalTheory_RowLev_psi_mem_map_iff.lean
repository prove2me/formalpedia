-- Prove2me | Theorems.Thm_GlobalTheory_RowLev_psi_mem_map_iff
-- name    : GlobalTheory.RowLev.psi_mem_map_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:32:54.609685+00:00
-- url     : https://prove2.me/theorems/71c43c3d-dd63-4cef-b566-548aef9bfbfa
-- title:
--   Row Lev: psi mem map iff
-- statement:
--   The Row Lev construction uses the psi mem map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralAdeleIdealOfIdealPrincipalAndInter.lean#L187-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/IntegralAdeleIdealOfIdealPrincipalAndInter.lean#L187-L226

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IntegralAdeleIdealOfIdealPrincipalAndInter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.RowLev
open Formalism.UG Formalism.UG.P Inhab
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.RowLev.psi_mem_map_iff (𝔞 : Ideal (𝓞 E)) (h : 𝔞 ≠ ⊥) (a : 𝓞 E) :
    psi F E a ∈ 𝔞.map (psi F E) ↔ a ∈ 𝔞 := by sorry
