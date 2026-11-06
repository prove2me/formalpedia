-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePowerReduction_surjective
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.primePowerReduction_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:40:59.685205+00:00
-- url     : https://prove2.me/theorems/181d9931-8595-4134-ad35-6e0bf0c85e20
-- title:
--   Centered Moment Correlation: prime Power Reduction surjective
-- statement:
--   The Centered Moment Correlation construction uses the prime Power Reduction surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L21-L23
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L21-L23

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Quotient.PowTransition
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_PrimePower
set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open NumberField
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
attribute [local instance] OAI.SevenEighths.CenteredMomentCorrelation._p2m_local_instance_3727eb8614_14
omit [NumberField K]

theorem OAI.SevenEighths.CenteredMomentCorrelation.primePowerReduction_surjective (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c) :
    Function.Surjective (primePowerReduction P hc) := by sorry
