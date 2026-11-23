-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_hasSatake_detRep
-- name    : GlobalTheory.SmGL.hasSatake_detRep
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:04.399452+00:00
-- url     : https://prove2.me/theorems/41d22fca-dcf8-456f-af9b-c4eae14ed849
-- title:
--   Sm GL: has Satake det Rep
-- statement:
--   The Sm GL construction uses the has Satake det Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L617-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsSubquotientDetRepParInd.lean#L617-L638

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
open GlobalTheory GlobalTheory.SmGL
open Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem GlobalTheory.SmGL.hasSatake_detRep {N : ℕ} {χ : kˣ →* ℂˣ} (h : IsUnram χ) {ϖ : kˣ}
    (hϖ : valuation k (ϖ : k) = uniformizer k) :
    HasSatake (detRep (Fin N) χ)
      fun i => χ ϖ * absPow k (((i : ℕ) : ℂ) - ((N : ℂ) - 1) / 2) ϖ := by sorry
