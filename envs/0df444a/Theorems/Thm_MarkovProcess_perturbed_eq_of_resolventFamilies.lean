-- Prove2me | Theorems.Thm_MarkovProcess_perturbed_eq_of_resolventFamilies
-- name    : MarkovProcess.perturbed_eq_of_resolventFamilies
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:30:42.072492+00:00
-- url     : https://prove2.me/theorems/870e3fcd-ce2a-46f9-a191-65c12c4ff235
-- title:
--   MarkovProcess: perturbed_eq_of_resolventFamilies
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

theorem MarkovProcess.perturbed_eq_of_resolventFamilies
    (R X Y : ℝ → (alpha → ℝ) → alpha → ℝ) {q : alpha → ℝ} {C : ℝ}
    (hR_add : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → R lam (f + g) = R lam f + R lam g)
    (hR_bound : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → ∀ {D : ℝ}, (∀ x, |f x| ≤ D) →
      ∀ x, |R lam f x| ≤ D / lam)
    (hq : Measurable q) (hq0 : ∀ x, 0 ≤ q x) (hqC : ∀ x, q x ≤ C)
    (hX_add : ∀ {lam : ℝ}, 0 < lam → ∀ {f g : alpha → ℝ},
      Measurable f → Measurable g → (∃ D, ∀ x, |f x| ≤ D) →
      (∃ D, ∀ x, |g x| ≤ D) → X lam (f + g) = X lam f + X lam g)
    (hX_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (X lam f))
    (hY_meas : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f))
    (hX_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      ∀ {D : ℝ}, (∀ x, |f x| ≤ D) → ∀ x, |X lam f x| ≤ D / lam)
    (hY_bound : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
      (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D)
    (hX_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X mu f = X lam f + (lam - mu) • X lam (X mu f))
    (hY_resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f))
    (hX_fixed : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      X lam f = R lam f - R lam (fun x ↦ q x * X lam f x))
    (hY_fixed : ∀ {lam : ℝ}, C < lam → 0 < lam → ∀ {f : alpha → ℝ},
      Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
      Y lam f = R lam f - R lam (fun x ↦ q x * Y lam f x))
    {lam : ℝ} (hlam : 0 < lam) {f : alpha → ℝ} (hf : Measurable f)
    {D : ℝ} (hfD : ∀ x, |f x| ≤ D) :
    X lam f = Y lam f := by sorry
