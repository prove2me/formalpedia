-- Prove2me | Theorems.Thm_MarkovProcess_IsKolmogorovProcess_ae_eventually_edist_unitDyadicGrid_le_natCast_mul_threshold
-- name    : MarkovProcess.IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_le_natCast_mul_threshold
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:32:25.206524+00:00
-- url     : https://prove2.me/theorems/ae940436-6c28-41f1-8128-422709af8828
-- title:
--   MarkovProcess: ae_eventually_edist_unitDyadicGrid_le_natCast_mul_threshold
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicChaining_a582e42e
import Definitions.Def_MarkovProcess_V3H_Continuity_DyadicIncrements_eff99a2c
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Process.Kolmogorov

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/

namespace MarkovProcess

section DyadicGridChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





end DyadicGridChaining

section DyadicMultiscale

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]





















end DyadicMultiscale

section DyadicAncestorChaining

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]











end DyadicAncestorChaining

section DyadicAncestorTail

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]







end DyadicAncestorTail

end MarkovProcess


open MarkovProcess
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Chaining across unit dyadic grids

This file merges the following former modules, one section each:

* `DyadicGridChaining`: Same-level chaining on dyadic grids
* `DyadicMultiscale`: Refinement and parent comparison for unit dyadic grids
* `DyadicAncestorChaining`: Finite chains of dyadic ancestors
* `DyadicAncestorTail`: Uniform tail bounds for finite dyadic ancestor chains
-/



open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} [PseudoEMetricSpace E]



open MarkovProcess in

theorem MarkovProcess.IsKolmogorovProcess.ae_eventually_edist_unitDyadicGrid_le_natCast_mul_threshold
    {P : Measure Ω} {X : NNRat → Ω → E} {p q γ : ℝ} {M : ℝ≥0}
    (hX : IsKolmogorovProcess X P p q M) (hγ : 0 < γ)
    (hγq : γ < (q - 1) / p) :
    ∀ᵐ ω ∂P, ∀ᶠ n in Filter.atTop, ∀ i j : Fin (2 ^ n + 1),
      (i : ℕ) ≤ j →
        edist (X (unitDyadicGrid n i) ω) (X (unitDyadicGrid n j) ω) ≤
          (j.val - i.val : ℕ) * dyadicIncrementThreshold γ n := by sorry
