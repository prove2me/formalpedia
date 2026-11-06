-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_solutionEquiv_val
-- name    : OAI.SevenEighths.ProbeGramCommon.solutionEquiv_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:50:50.882081+00:00
-- url     : https://prove2.me/theorems/32574113-27b1-4bb7-abc8-14a71e29df57
-- title:
--   Probe Gram Common: solution Equiv val
-- statement:
--   The Probe Gram Common construction uses the solution Equiv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonParam.lean#L100-L102
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonParam.lean#L100-L102

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_FullCorrelation
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]

theorem OAI.SevenEighths.ProbeGramCommon.solutionEquiv_val (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1) (t : ResidueQ C) :
    (solutionEquiv C n₁ n₂ a b k hC hn₁ hab t).val=(leftParam C n₁ b k t,rightParam C n₂ a k t) := by sorry

attribute [defeq] OAI.SevenEighths.ProbeGramCommon.solutionEquiv_val
