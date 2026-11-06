-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_fullCorrelation_bezout
-- name    : OAI.SevenEighths.ProbeGramCommon.fullCorrelation_bezout
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:55.225208+00:00
-- url     : https://prove2.me/theorems/bb4c0a16-7a09-4886-ac8c-4d96eeffbfe6
-- title:
--   Probe Gram Common: full Correlation bezout
-- statement:
--   The Probe Gram Common construction uses the full Correlation bezout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonLinear.lean#L27-L43
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonLinear.lean#L27-L43

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonLinear
set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {R : Type*} [CommRing R]

theorem OAI.SevenEighths.ProbeGramCommon.fullCorrelation_bezout [Fintype R] (n₁ n₂ a b k : R) (hab : a*n₁+b*n₂=1)
    (f g : R→ℂ) :
    fullCorrelation (fun x=>n₂*x) (fun y=>n₁*y) f g k=
      ∑t : R,f (b*k+n₁*t)*star (g (-a*k+n₂*t)) := by sorry
