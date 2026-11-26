-- Prove2me | Theorems.Thm_Malliavin_BrownianIteratedConstruction_span_range_eq_top_of_isMonicOfDegree
-- name    : Malliavin.BrownianIteratedConstruction.span_range_eq_top_of_isMonicOfDegree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:24.475135+00:00
-- url     : https://prove2.me/theorems/b74c7947-7ee8-49f7-8f10-47853e720c36
-- title:
--   Brownian Iterated Construction: span range eq top of is Monic Of Degree
-- statement:
--   A degree-indexed monic polynomial family spans the full polynomial ring.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L38-L72
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/BrownianHermite.lean#L38-L72

import Definitions.Def_Malliavin_BrownianMultipleIntegral
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Definitions.Def_Malliavin_BrownianHermite
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Malliavin Malliavin.BrownianIteratedConstruction

theorem Malliavin.BrownianIteratedConstruction.span_range_eq_top_of_isMonicOfDegree (p : ℕ → Polynomial ℝ)
    (hp : ∀ n, Polynomial.IsMonicOfDegree (p n) n) :
    Submodule.span ℝ (Set.range p) = ⊤ := by sorry
