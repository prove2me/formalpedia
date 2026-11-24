-- Prove2me | Theorems.Thm_GlobalTheory_MinorFrame_inv_le_span_prodMinors
-- name    : GlobalTheory.MinorFrame.inv_le_span_prodMinors
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:35:55.560113+00:00
-- url     : https://prove2.me/theorems/65d6fc49-d736-4243-9da9-a441c7f91326
-- title:
--   Minor Frame: inv le span prod Minors
-- statement:
--   The Minor Frame construction uses the inv le span prod Minors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockDetCharInvariantsLeSpanProdMaximalMinors.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FockDetCharInvariantsLeSpanProdMaximalMinors.lean#L45-L69

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetGNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryGroupFamilyZariskiDenseStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockPairingLinearSubstitutionAdjointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CauchyBinetColumnFrameProdDetPowEqSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FockDetCharInvariantsLeSpanProdMaximalMinors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.MinorFrame
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.MinorFrame.inv_le_span_prodMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by sorry
