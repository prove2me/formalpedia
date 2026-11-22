-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_JumpFormula_measurable_uncurry_cadlagRep
-- name    : LevyStochCalc.Ito.JumpFormula.measurable_uncurry_cadlagRep
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T12:52:38.098635+00:00
-- url     : https://prove2.me/theorems/ba3c5d21-971a-47f8-967f-4b9ec8fc26d4
-- title:
--   measurable uncurry cadlagRep
-- statement:
--   The source theorem `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_cadlagRep` is extracted from `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoLevyBoundedDerivsSolutionRepresentative_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The càdlàg representative of a solution path

The Itô–Lévy formula at bounded derivatives asks for left limits of the solution at every sample
point and every time, while the well-posedness theorem produces paths that are càdlàg only on a
measurable set `G` of full measure. `cadlagRep G X` is the path map that agrees with `X` on `G` at
nonnegative times, is the constant zero path off `G`, and is frozen at the zero state before time
zero. It is càdlàg at every sample point and every time, adapted whenever `G` belongs to the
initial σ-algebra, progressively measurable because it is right-continuous everywhere, and solves
the equation on every window, because both stochastic integrals depend only on the class of their
integrand.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section CadlagRep

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

variable {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}

theorem _root_.LevyStochCalc.Ito.JumpFormula.measurable_uncurry_cadlagRep (hGm : MeasurableSet G)
    (hX : Measurable (Function.uncurry X)) :
    Measurable (Function.uncurry (cadlagRep G X)) := by sorry
