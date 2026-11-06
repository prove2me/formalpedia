-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePower_localCorrelation_first_zero
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.primePower_localCorrelation_first_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:38:46.162796+00:00
-- url     : https://prove2.me/theorems/dde03aad-ddd0-4137-bacc-19a088f42786
-- title:
--   Centered Moment Correlation: prime Power local Correlation first zero
-- statement:
--   The Centered Moment Correlation construction uses the prime Power local Correlation first zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L107-L127
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L107-L127

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
variable (P : Ideal (𝓞 K)) [P.IsMaximal] {c : ℕ} (hc : 1 ≤ c)
variable [Fintype (𝓞 K ⧸ P ^ c)] [Fintype (𝓞 K ⧸ P)]
attribute [local instance] OAI.SevenEighths.CenteredMomentCorrelation._p2m_local_instance_3727eb8614_57

theorem OAI.SevenEighths.CenteredMomentCorrelation.primePower_localCorrelation_first_zero (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (hχ : orderOf χ = 6) (u : 𝓞 K ⧸ P ^ c) (v : (𝓞 K ⧸ P ^ c)ˣ)
    (k : 𝓞 K ⧸ P ^ c) (hu : primePowerReduction P hc u = 0) :
    fullCorrelation (fun x => (v : 𝓞 K ⧸ P ^ c) * x) (fun y => u * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      (if 6 ∣ c ∧ primePowerReduction P hc k ≠ 0
       then (Ideal.absNorm P : ℂ) - 1 else 0) := by sorry
