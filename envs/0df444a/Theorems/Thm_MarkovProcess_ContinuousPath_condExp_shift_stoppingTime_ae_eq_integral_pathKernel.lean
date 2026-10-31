-- Prove2me | Theorems.Thm_MarkovProcess_ContinuousPath_condExp_shift_stoppingTime_ae_eq_integral_pathKernel
-- name    : MarkovProcess.ContinuousPath.condExp_shift_stoppingTime_ae_eq_integral_pathKernel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T09:31:48.32905+00:00
-- url     : https://prove2.me/theorems/96812b5f-a0a3-4c79-9c6b-70c0477caaff
-- title:
--   MarkovProcess: condExp_shift_stoppingTime_ae_eq_integral_pathKernel
-- statement:
--   Source-faithful Lean theorem from Scott Armstrong's MarkovProcess formalisation. The exact hypotheses and mathematical conclusion appear in the formal statement.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_Path_Shift_e538a06a
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Process.Stopping
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Conditional restart at countable-valued stopping times

This file upgrades deterministic-time conditional restart identities to a finite-valued or,
more generally, countable-valued finite stopping time.  It is ordinary conditional probability
infrastructure: the deterministic-time restart identity is a hypothesis here, proved for the
continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
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
# Conditional restart at countable-valued stopping times

This file upgrades deterministic-time conditional restart identities to a finite-valued or,
more generally, countable-valued finite stopping time.  It is ordinary conditional probability
infrastructure: the deterministic-time restart identity is a hypothesis here, proved for the
continuous-path process in `Trajectory/FellerRestrictedRestart.lean`.
-/

open MeasureTheory ProbabilityTheory



variable {alpha E : Type*} [TopologicalSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]







open MarkovProcess.ContinuousPath in

theorem MarkovProcess.ContinuousPath.condExp_shift_stoppingTime_ae_eq_integral_pathKernel
    (Q : Kernel alpha (ContinuousPath alpha)) [IsMarkovKernel Q]
    (x : alpha) (tau : ContinuousPath alpha → NNReal)
    (htau : IsStoppingTime (canonicalFiltration (alpha := alpha))
      (fun omega ↦ (tau omega : WithTop NNReal)))
    (htauRange : (Set.range tau).Countable)
    (hRestart : ∀ (S : NNReal) (A : Set (ContinuousPath alpha)),
      MeasurableSet[canonicalFiltration (alpha := alpha) S] A →
        ((Q x).restrict A).map (shift S) =
          Kernel.comap Q (coordinateProcess (alpha := alpha) S)
              (measurable_coordinateProcess S) ∘ₘ ((Q x).restrict A))
    (F : ContinuousPath alpha → E) (hF : StronglyMeasurable F)
    (C : Real) (hFC : ∀ eta, ‖F eta‖ ≤ C) :
    (Q x)[fun omega ↦ F (shift (tau omega) omega)|htau.measurableSpace] =ᵐ[Q x]
      fun omega ↦ ∫ eta, F eta ∂Q (omega (tau omega)) := by sorry
