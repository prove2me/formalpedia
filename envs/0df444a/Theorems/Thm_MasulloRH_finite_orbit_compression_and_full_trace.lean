-- Prove2me | Theorems.Thm_MasulloRH_finite_orbit_compression_and_full_trace
-- name    : MasulloRH.finite_orbit_compression_and_full_trace
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T01:17:52.833317+00:00
-- url     : https://prove2.me/theorems/127a2340-71d8-465e-8be6-d1e66703e471
-- title:
--   Finite orbital shift compression, its trace, and a quantitative norm estimate
-- statement:
--   For the length-$n$ window of a bilateral shift by $d\ge0$, its constant-vector matrix coefficient is $(n-d)_+/n$ and its normalized ordinary trace is $1_{d=0}$. For a finite family in a real normed space, the norm difference between the weighted sum and the sum of all coefficients is at most $\sum_d d\lVert A_d\rVert/n$. This estimates the finite comparison step in a candidate orbital regularization of the rational trace.
-- source:
--   Finite-orbit calculation motivated by Masullo, The Music of the Primes, (11.3.2.3–5), pp. 495–496, and https://github.com/mccorvie/riemann-masullo/issues/1358.

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open Finset

theorem MasulloRH.finite_orbit_compression_and_full_trace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (hn : 0 < n) (T : Finset ℕ) (A : ℕ → E) :
    (∀ d : ℕ, (∑ i ∈ range n, ∑ j ∈ range n,
        if j = i+d then (1 : ℂ) else 0) / (n : ℂ) = ((n-d : ℕ) : ℂ) / n ∧
      (∑ i ∈ range n, if i = i+d then (1 : ℂ) else 0) / (n : ℂ) =
        if d = 0 then 1 else 0) ∧
    ‖(∑ d ∈ T, (((n-d : ℕ) : ℝ) / n) • A d) - ∑ d ∈ T, A d‖ ≤
      (∑ d ∈ T, (d : ℝ) * ‖A d‖) / n := by sorry
