-- Prove2me | Theorems.Thm_GlobalTheory_GaussHerm_integral_exp_neg_herm
-- name    : GlobalTheory.GaussHerm.integral_exp_neg_herm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:51:10.329823+00:00
-- url     : https://prove2.me/theorems/4cbb9950-098e-4731-83d3-f24d13cace2a
-- title:
--   Gauss Herm: integral exp neg herm
-- statement:
--   The Gauss Herm construction uses the integral exp neg herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralExpNegHermitianFormPosDef.lean#L46-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralExpNegHermitianFormPosDef.lean#L46-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.GaussHerm

theorem GlobalTheory.GaussHerm.integral_exp_neg_herm : ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef →
    Integrable (fun w : V n => Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re)) ∧
    ∫ w : V n, Real.exp (-(∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re) =
      Real.pi ^ n / H.det.re := by sorry
