-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_fullCorrelation_bezout_norm
-- name    : OAI.SevenEighths.ProbeGramCommon.fullCorrelation_bezout_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:01:55.925124+00:00
-- url     : https://prove2.me/theorems/103df792-cfd7-409a-a060-97b8935dfab8
-- title:
--   Probe Gram Common: full Correlation bezout norm
-- statement:
--   The Probe Gram Common construction uses the full Correlation bezout norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonLinear.lean#L45-L56
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonLinear.lean#L45-L56

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonLinear
set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

theorem OAI.SevenEighths.ProbeGramCommon.fullCorrelation_bezout_norm [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) (hf : ∀x,‖f x‖≤1) (hg : ∀x,‖g x‖≤1) :
    ‖fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k‖≤(Fintype.card R:ℝ) := by sorry
