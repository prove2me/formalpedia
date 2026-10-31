-- Prove2me | Theorems.Thm_MarkovProcess_perturbed_unique
-- name    : MarkovProcess.perturbed_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:25:57.128812+00:00
-- url     : https://prove2.me/theorems/a66627aa-7737-4965-8521-94f57092b987
-- title:
--   MarkovProcess: perturbed_unique
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Kernel_Operator_8b41d3bf
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.MeasurableIntegral

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Uniqueness for resolvents on bounded measurable functions

This file proves three elementary contraction principles for maps acting on bounded measurable
real functions. The first gives uniqueness for a bounded multiplicative perturbation equation.
The second propagates equality of two resolvent families from all sufficiently large shifts to
every positive shift by the resolvent identity. The third combines the first two principles.

Main results: `perturbed_unique`, `resolventFamily_eq_of_eventually`, and
`perturbed_eq_of_resolventFamilies`.

The operators are plain maps on functions; no Banach-space carrier or continuity is asserted.
-/

open Filter

namespace MarkovProcess

noncomputable section



variable {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]







end

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Uniqueness for resolvents on bounded measurable functions

This file proves three elementary contraction principles for maps acting on bounded measurable
real functions. The first gives uniqueness for a bounded multiplicative perturbation equation.
The second propagates equality of two resolvent families from all sufficiently large shifts to
every positive shift by the resolvent identity. The third combines the first two principles.

Main results: `perturbed_unique`, `resolventFamily_eq_of_eventually`, and
`perturbed_eq_of_resolventFamilies`.

The operators are plain maps on functions; no Banach-space carrier or continuity is asserted.
-/

open Filter





variable {alpha : Type*} [MeasurableSpace alpha] [Nonempty alpha]

open MarkovProcess in

theorem MarkovProcess.perturbed_unique
    (R X Y : (alpha → ℝ) → alpha → ℝ) {q : alpha → ℝ} {C lam : ℝ}
    (hR_add : ∀ {f g : alpha → ℝ}, Measurable f → Measurable g →
      (∃ D, ∀ x, |f x| ≤ D) → (∃ D, ∀ x, |g x| ≤ D) → R (f + g) = R f + R g)
    (hR_bound : ∀ {f : alpha → ℝ}, Measurable f → ∀ {D : ℝ},
      (∀ x, |f x| ≤ D) → ∀ x, |R f x| ≤ D / lam)
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (hqC : ∀ x, q x ≤ C) (hlam : C < lam)
    (hX_meas : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Measurable (X f))
    (hY_meas : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Measurable (Y f))
    (hX_bound : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      ∃ D, ∀ x, |X f x| ≤ D)
    (hY_bound : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      ∃ D, ∀ x, |Y f x| ≤ D)
    (hX_fixed : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X f = R f - R (fun x ↦ q x * X f x))
    (hY_fixed : ∀ {f : alpha → ℝ}, Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y f = R f - R (fun x ↦ q x * Y f x))
    {f : alpha → ℝ} (hf : Measurable f) {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X f = Y f := by sorry
