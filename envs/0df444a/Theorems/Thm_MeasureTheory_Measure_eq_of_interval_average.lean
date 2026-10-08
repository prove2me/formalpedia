-- Prove2me | Theorems.Thm_MeasureTheory_Measure_eq_of_interval_average
-- name    : MeasureTheory.Measure.eq_of_interval_average
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-05T00:27:44.057988+00:00
-- url     : https://prove2.me/theorems/ac672c24-3a72-48a3-b2b3-69e06afe713c
-- title:
--   Finite measures are determined by their averaged open and closed interval masses
-- statement:
--   Let $\mu,\nu$ be finite Borel measures on $\mathbb R$. Suppose that for every $a<b$,
--
--   $$\frac{\mu((a,b))+\mu([a,b])}{2}=\frac{\nu((a,b))+\nu([a,b])}{2}.$$
--
--   Then $\mu=\nu$. No assumption that either measure has no atoms is needed. This is the measure-determination step in Stieltjes inversion.
-- source:
--   G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), p. 108, Theorem 3.21 and its proof, Eq. (3.89); https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf (PDF p. 119).

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set
open scoped Topology

theorem MeasureTheory.Measure.eq_of_interval_average (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a b : ℝ, a < b →
      ((μ (Ioo a b)).toReal + (μ (Icc a b)).toReal) / 2 =
      ((ν (Ioo a b)).toReal + (ν (Icc a b)).toReal) / 2) : μ = ν := by sorry
