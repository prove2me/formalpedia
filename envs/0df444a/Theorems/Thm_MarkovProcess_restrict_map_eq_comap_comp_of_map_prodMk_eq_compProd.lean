-- Prove2me | Theorems.Thm_MarkovProcess_restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd
-- name    : MarkovProcess.restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T17:56:15.531976+00:00
-- url     : https://prove2.me/theorems/6cf9b46f-422d-49a0-a2c1-7e868087812c
-- title:
--   Restricted conditional future laws from a factorised joint law
-- statement:
--   If the joint measure of a conditioning variable and a future variable factors as a marginal measure composed with a transition kernel, then restricting the original measure to any event measurable with respect to the conditioning variable preserves the corresponding conditional future-kernel identity.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Restart/RestrictedRestartOfJoint.lean#L30-L52

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.CompNotation
open MeasureTheory ProbabilityTheory
variable {Omega beta gamma : Type*} {mOmega : MeasurableSpace Omega}
  {mBeta : MeasurableSpace beta} {mGamma : MeasurableSpace gamma}

theorem MarkovProcess.restrict_map_eq_comap_comp_of_map_prodMk_eq_compProd
    (mu : @Measure Omega mOmega) [SFinite mu]
    (X : Omega → beta) (hX : @Measurable Omega beta mOmega mBeta X)
    (Y : Omega → gamma) (hY : @Measurable Omega gamma mOmega mGamma Y)
    (kappa : @Kernel beta gamma mBeta mGamma) [IsSFiniteKernel kappa]
    (hJoint : mu.map (fun omega ↦ (X omega, Y omega)) = (mu.map X) ⊗ₘ kappa) :
    ∀ A : Set Omega, MeasurableSet[mBeta.comap X] A →
      (mu.restrict A).map Y =
        (Kernel.comap kappa X hX) ∘ₘ (mu.restrict A) := by sorry
