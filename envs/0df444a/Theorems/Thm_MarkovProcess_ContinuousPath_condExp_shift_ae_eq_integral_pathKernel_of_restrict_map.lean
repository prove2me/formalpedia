-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
-- name    : MarkovProcess.ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:26:20.488325+00:00
-- url     : https://prove2.me/theorems/7843ead4-94fb-4c94-9240-393441042b69
-- title:
--   MarkovProcess: condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic-time conditional restart on continuous paths

This file specializes the generic conditional-expectation bridge to canonical continuous-path
space.  The required input is the full future restart identity after restriction to every event in
the canonical filtration at the restart time.  An unconditional shifted-law identity is only the
special case of the input for the whole path space and does not imply the result below.

The theorem is a conditional API: it does not prove its restricted restart-law hypothesis and does
not by itself associate a Markov or Hunt process with a transition semigroup.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]



end
end ContinuousPath
end MarkovProcess


open MarkovProcess
open MarkovProcess.ContinuousPath
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Deterministic-time conditional restart on continuous paths

This file specializes the generic conditional-expectation bridge to canonical continuous-path
space.  The required input is the full future restart identity after restriction to every event in
the canonical filtration at the restart time.  An unconditional shifted-law identity is only the
special case of the input for the whole path space and does not imply the result below.

The theorem is a conditional API: it does not prove its restricted restart-law hypothesis and does
not by itself associate a Markov or Hunt process with a transition semigroup.
-/

open MeasureTheory ProbabilityTheory



variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (S : NNReal)
    (hRestart : ∀ A : Set (ContinuousPath alpha),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (Q x)[fun omega ↦ F (shift S omega)|canonicalFiltration (alpha := alpha) S] =ᵐ[Q x]
      fun omega ↦ ∫ eta, F eta ∂Q (omega S) := by sorry
