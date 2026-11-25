-- Prove2me | Theorems.Thm_GlobalTheory_PrinTwo_coord_nU
-- name    : GlobalTheory.PrinTwo.coord_nU
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:42.595847+00:00
-- url     : https://prove2.me/theorems/59836548-0b02-49db-8df1-633222fcb9f6
-- title:
--   Prin Two: coord n U
-- statement:
--   The Prin Two construction uses the coord n U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L172-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WEMulNUMulTD.lean#L172-L174

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

theorem GlobalTheory.PrinTwo.coord_nU {μ₁ μ₂ : kˣ →* ℂˣ} (f : PSp μ₁ μ₂) (y x : k) :
    coord (psRep μ₁ μ₂ (nU y) f) x = coord f (x + y) := by sorry
