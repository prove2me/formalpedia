-- Prove2me | Theorems.Thm_MarkovProcess_condExp_comp_ae_eq_integral_kernel_of_restrict_map
-- name    : MarkovProcess.condExp_comp_ae_eq_integral_kernel_of_restrict_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:56:15.43302+00:00
-- url     : https://prove2.me/theorems/b261889e-38b2-4615-b7d9-6ba876928afe
-- title:
--   Conditional expectation from event-restricted future kernel laws
-- statement:
--   For a finite measure and a Markov kernel, equality of all event-restricted future laws implies that the conditional expectation of every uniformly bounded strongly measurable future observable is the integral of that observable against the transition kernel.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Restart/ConditionalExpectation.lean#L33-L79

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
open MeasureTheory ProbabilityTheory
variable {Omega beta E : Type*} {m : MeasurableSpace Omega}
  {mOmega : MeasurableSpace Omega} {mBeta : MeasurableSpace beta}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

theorem MarkovProcess.condExp_comp_ae_eq_integral_kernel_of_restrict_map
    (mu : @Measure Omega mOmega) [IsFiniteMeasure mu]
    (kappa : @Kernel Omega beta mOmega mBeta) [IsMarkovKernel kappa]
    (Y : Omega → beta) (hY : @Measurable Omega beta mOmega mBeta Y)
    (hm : m ≤ mOmega)
    (hJoint : ∀ A : Set Omega, MeasurableSet[m] A →
      (mu.restrict A).map Y = kappa ∘ₘ (mu.restrict A))
    (F : beta → E) (hF : StronglyMeasurable F)
    (hFm : StronglyMeasurable[m] (fun omega ↦ ∫ y, F y ∂kappa omega))
    (C : Real) (hFC : ∀ y, ‖F y‖ ≤ C) :
    mu[fun omega ↦ F (Y omega)|m] =ᵐ[mu]
      fun omega ↦ ∫ y, F y ∂kappa omega := by sorry
