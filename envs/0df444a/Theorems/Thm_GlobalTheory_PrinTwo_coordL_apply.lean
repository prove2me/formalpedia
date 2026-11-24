-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_coordL_apply
-- name    : GlobalTheory.PrinTwo.coordL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:52:57.700801+00:00
-- url     : https://prove2.me/theorems/2034fed3-8f31-4381-9c86-901682bac354
-- title:
--   Prin Two: coord L apply
-- statement:
--   The Prin Two construction uses the coord L apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L170-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L170-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WEMulNUMulTD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
open GlobalTheory GlobalTheory.PrinTwo
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.PrinTwo.coordL_apply (μ₁ μ₂ : kˣ →* ℂˣ) (f : PSp μ₁ μ₂) : coordL μ₁ μ₂ f = coord f := by sorry

attribute [defeq] GlobalTheory.PrinTwo.coordL_apply
