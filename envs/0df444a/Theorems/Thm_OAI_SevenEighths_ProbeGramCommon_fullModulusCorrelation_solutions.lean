-- Prove2me | Theorems.Thm_OAI_SevenEighths_ProbeGramCommon_fullModulusCorrelation_solutions
-- name    : OAI.SevenEighths.ProbeGramCommon.fullModulusCorrelation_solutions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:27:43.988322+00:00
-- url     : https://prove2.me/theorems/a2f5195f-40aa-4c4d-9cee-169bb7d43c89
-- title:
--   Probe Gram Common: full Modulus Correlation solutions
-- statement:
--   The Probe Gram Common construction uses the full Modulus Correlation solutions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonSum.lean#L12-L25
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonSum.lean#L12-L25

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonSum
set_option autoImplicit false
open OAI
noncomputable section
open scoped Classical
open OAI.SevenEighths OAI.SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
omit [IsDomain A]

theorem OAI.SevenEighths.ProbeGramCommon.fullModulusCorrelation_solutions (C n₁ n₂ k : A)
    [Fintype (ResidueQ (C*n₁))] [Fintype (ResidueQ (C*n₂))]
    (χ : MulChar (ResidueQ (C*n₁)) ℂ) (ψ : MulChar (ResidueQ (C*n₂)) ℂ) :
    fullModulusCorrelation (C*n₁) (C*n₂) χ ψ (C*k)=
      ∑p : Solutions C n₁ n₂ k,χ p.val.1*star (ψ p.val.2) := by sorry
