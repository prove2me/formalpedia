-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_fullModulusCorrelation_parameter
-- name    : OAI.SevenEighths.ProbeGramCommon.fullModulusCorrelation_parameter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:02:03.28023+00:00
-- url     : https://prove2.me/theorems/1b67ffbf-5c40-49fa-bcd9-1810ab0b5cb3
-- title:
--   Probe Gram Common: full Modulus Correlation parameter
-- statement:
--   The Probe Gram Common construction uses the full Modulus Correlation parameter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonSum.lean#L27-L35
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonSum.lean#L27-L35

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonSum
set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]

theorem OAI.SevenEighths.ProbeGramCommon.fullModulusCorrelation_parameter (C n₁ n₂ a b k : A) (hC : C≠0) (hn₁ : n₁≠0)
    (hab : a*n₁+b*n₂=1)
    [Fintype (ResidueQ C)] [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑t : ResidueQ C,χ (leftParam C n₁ b k t)*star (ψ (rightParam C n₂ a k t)) := by sorry
