-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePowerCharacter_apply
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.primePowerCharacter_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:38:44.516649+00:00
-- url     : https://prove2.me/theorems/be9d5cbb-aabd-4d2b-9364-640696770b71
-- title:
--   Centered Moment Correlation: prime Power Character apply
-- statement:
--   The Centered Moment Correlation construction uses the prime Power Character apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L50-L52
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L50-L52

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

theorem OAI.SevenEighths.CenteredMomentCorrelation.primePowerCharacter_apply (P : Ideal (𝓞 K)) {c : ℕ} (hc : 1 ≤ c)
    (χ : MulChar (𝓞 K ⧸ P) ℂ) (x : 𝓞 K ⧸ P ^ c) :
    primePowerCharacter P hc χ x = χ (primePowerReduction P hc x) := by sorry

attribute [defeq] OAI.SevenEighths.CenteredMomentCorrelation.primePowerCharacter_apply
