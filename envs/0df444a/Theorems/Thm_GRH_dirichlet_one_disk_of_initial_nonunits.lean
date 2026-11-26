-- Prove2me | Theorems.Thm_GRH_dirichlet_one_disk_of_initial_nonunits
-- name    : GRH.dirichlet_one_disk_of_initial_nonunits
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:34:09.040806+00:00
-- url     : https://prove2.me/theorems/72587df8-cfc5-5c4d-aea2-4e4d06473f5a
-- title:
--   A totient bound for a Dirichlet L-function following a gap in the unit residues
-- statement:
--   Suppose $q>2$, $M\ge1$, and each integer from $2$ through $M$ shares a prime factor with $q$. For every nonprincipal character modulo $q$ and every $s$ with $x=\Re s>0$, we have $|L(s,\chi)-1|\le(\varphi(q)/4)(1+|s|/x)(M+1)^{-x}$.
-- source:
--   Developed for the centered Möbius bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive grid condition at https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a. The centered-prefix estimate uses the published power variation bound at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965 and Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.Nat.Totient

theorem GRH.dirichlet_one_disk_of_initial_nonunits (q : ℕ) [NeZero q] (hq : 2 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (M : ℕ) (hM : 0 < M) (hgap : ∀ k : ℕ, 2 ≤ k → k ≤ M → ¬ k.Coprime q)
    (s : ℂ) (hs : 0 < s.re) :
    ‖χ.LFunction s - 1‖ ≤ ((q.totient:ℝ)/4)*(1+‖s‖/s.re)*((M:ℝ)+1)^(-s.re) := by sorry
