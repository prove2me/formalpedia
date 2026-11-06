-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_primePower_localCorrelation
-- name    : OAI.SevenEighths.CenteredMomentCorrelation.primePower_localCorrelation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:42:17.395821+00:00
-- url     : https://prove2.me/theorems/3e26d522-b691-4a84-9686-d691297e853a
-- title:
--   Centered Moment Correlation: prime Power local Correlation
-- statement:
--   The Centered Moment Correlation construction uses the prime Power local Correlation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L59-L69
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Moments/PrimePower.lean#L59-L69

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

theorem OAI.SevenEighths.CenteredMomentCorrelation.primePower_localCorrelation (χ : MulChar (𝓞 K ⧸ P) ℂ)
    (u : (𝓞 K ⧸ P ^ c)ˣ) (v k : 𝓞 K ⧸ P ^ c) :
    fullCorrelation (fun x => v * x) (fun y => (u : 𝓞 K ⧸ P ^ c) * y)
      (fun x => (χ ^ c) (primePowerReduction P hc x))
      (fun y => (χ ^ c) (primePowerReduction P hc y)) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      localCorrelation (χ ^ c) (primePowerReduction P hc u)
        (primePowerReduction P hc v) (primePowerReduction P hc k) := by sorry
