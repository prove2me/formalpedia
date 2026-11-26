-- Prove2me | Theorems.Thm_GRH_dirichlet_one_disk_of_period_variation
-- name    : GRH.dirichlet_one_disk_of_period_variation
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:34:09.191848+00:00
-- url     : https://prove2.me/theorems/8872c828-b48c-5340-b974-c0f96bdccb5a
-- title:
--   A two-arc bound for a complete character period controls the distance from one
-- statement:
--   Split a complete nonprincipal character period into two arcs on each of which the sum of the coefficient magnitudes is at most $V$. If $\chi(2),\ldots,\chi(M)$ vanish and $M\ge1$, then $|L(s,\chi)-1|\le(V/2)(1+|s|/x)(M+1)^{-x}$ for every $x=\Re s>0$.
-- source:
--   Developed for the centered Möbius bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive grid condition at https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a. The centered-prefix estimate uses the published power variation bound at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965 and Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.Nat.Totient

theorem GRH.dirichlet_one_disk_of_period_variation (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t M : ℕ) (V : ℝ) (ht : t ≤ q) (hM : 0 < M)
    (hl : (∑ k ∈ Finset.range t, ‖χ ((k+1:ℕ):ZMod q)‖) ≤ V)
    (hr : (∑ k ∈ Finset.Ico t q, ‖χ ((k+1:ℕ):ZMod q)‖) ≤ V)
    (hzero : ∀ k : ℕ, 0 < k → k < M → χ ((k+1:ℕ):ZMod q) = 0)
    (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s - 1‖ ≤ (V/2)*(1+‖s‖/s.re)*((M:ℝ)+1)^(-s.re) := by sorry
