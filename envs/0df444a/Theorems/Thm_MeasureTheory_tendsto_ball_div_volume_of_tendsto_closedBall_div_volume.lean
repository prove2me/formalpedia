-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_ball_div_volume_of_tendsto_closedBall_div_volume
-- name    : MeasureTheory.tendsto_ball_div_volume_of_tendsto_closedBall_div_volume
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T22:31:02.949471+00:00
-- url     : https://prove2.me/theorems/450269f5-db2d-40bc-8ea3-a290f1131fc3
-- title:
--   Transfer closed-ball density limits to open balls on the real line
-- statement:
--   Let μ be any measure on the real line, x a point, and d an extended nonnegative real number. If the closed-ball density tends to d, then the open-ball density has the same limit:
--
--   $$\lim_{r\downarrow0}\frac{\mu(\overline B_r(x))}{2r}=d\quad\Longrightarrow\quad\lim_{r\downarrow0}\frac{\mu(B_r(x))}{2r}=d.$$
--
--   This pointwise transfer permits reuse of closed-ball differentiation theorems for symmetric open intervals. It includes infinite limits and measures with atoms; no finiteness hypothesis is imposed.
-- source:
--   Supporting pointwise normalization lemma for G. Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99 (2009), Theorem A.37, p. 286, and derivative definition (A.44), pp. 282–283; https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf. Derived by nesting closedBall(x,r/(1+r)), ball(x,r), closedBall(x,r) and the Lebesgue volume formula 2r; generalized to arbitrary measures and extended limits.

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

open MeasureTheory Filter Metric
open scoped ENNReal Topology

theorem MeasureTheory.tendsto_ball_div_volume_of_tendsto_closedBall_div_volume (μ : Measure ℝ) (x : ℝ) (d : ℝ≥0∞)
    (h : Tendsto (fun r : ℝ => μ (closedBall x r) / volume (closedBall x r))
      (𝓝[>] (0 : ℝ)) (𝓝 d)) :
    Tendsto (fun r : ℝ => μ (ball x r) / volume (ball x r))
      (𝓝[>] (0 : ℝ)) (𝓝 d) := by sorry
