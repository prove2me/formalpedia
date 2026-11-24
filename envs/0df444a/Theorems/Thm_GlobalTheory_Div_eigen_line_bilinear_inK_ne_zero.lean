-- Prove2me | Theorems.Thm_GlobalTheory_Div_eigen_line_bilinear_inK_ne_zero
-- name    : GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:50:37.667396+00:00
-- url     : https://prove2.me/theorems/aecde20c-8996-47a8-827e-e38f583ea57b
-- title:
--   eigen line bilinear: in K ne zero
-- statement:
--   The eigen line bilinear construction uses the in K ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodProductIntegral.lean#L18-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.eigen_line_bilinear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}

theorem GlobalTheory.Div.eigen_line_bilinear.inK_ne_zero (hfree : Module.Free O H) {h : H} (hh : h ≠ 0) : inK (O := O) K H h ≠ 0 := by sorry
