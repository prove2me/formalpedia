-- Prove2me | Theorems.Thm_MasulloRH_all_cell_pole_autocorrelation_and_exact_geometric_compensation
-- name    : MasulloRH.all_cell_pole_autocorrelation_and_exact_geometric_compensation
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T19:21:14.804803+00:00
-- url     : https://prove2.me/theorems/9f8d3d6f-1c98-4e15-8ab8-eee4e526ae48
-- title:
--   All log-cell overlaps of the reference pole and exact geometric compensation at every positive lag
-- statement:
--   Take a positive cell length L, r=exp(-L/2), q=r², and the reference pole profile g(k,x)=-r^(k+1) exp(x/2) in the local coordinate of cell k. For delay mL+s, 0<=s<=L, compute the first contributing cell and each subsequent two-piece adjacent-cell integral. They are respectively r^m(exp(-s/2)-q exp(s/2)) and r^m q^(k+1)(1-q) exp(s/2). Against an arbitrary continuous test f on [0,L], the latter integrals form a convergent series of exact sum r^m q times the positive half-moment. Adding the first term leaves precisely r^m times the negative half-moment. This includes every prime with L=log p, arbitrary integer-cell translates, and exact cancellation on half-moment-zero tests.
-- source:
--   Masullo mission, all-cell extension of the reference pole calculation in the real half moment on the first global cell. This theorem certifies the explicit reference profile, including arbitrary shifted cells.

import Mathlib
open MeasureTheory

theorem MasulloRH.all_cell_pole_autocorrelation_and_exact_geometric_compensation (L : ℝ) (hL : 0 < L) (m : ℕ) (f : ℝ → ℝ) (hf : Continuous f) :
    let r := Real.exp (-L/2)
    let q := r*r
    let g := fun (k : ℕ) (x : ℝ) => -(r^(k+1))*Real.exp (x/2)
    let first := fun s : ℝ => ∫ x in s..L, g m x * g 0 (x-s)
    let later := fun (k : ℕ) (s : ℝ) =>
      (∫ x in (0:ℝ)..s, g (k+1+m) x * g k (x-s+L)) +
      (∫ x in s..L, g (k+1+m) x * g (k+1) (x-s))
    let test := fun (F : ℝ → ℝ) => ∫ s in (0:ℝ)..L, f s * F s
    (∀ s ∈ Set.Icc 0 L, first s =
        r^m * (Real.exp (-s/2) - q * Real.exp (s/2)) ∧
      (∀ k, later k s = r^m * q^(k+1) * (1-q) * Real.exp (s/2))) ∧
    HasSum (fun k => test (later k))
      (r^m * q * test (fun s => Real.exp (s/2))) ∧
    test first + (∑' k : ℕ, test (later k)) =
      r^m * test (fun s => Real.exp (-s/2)) := by sorry
