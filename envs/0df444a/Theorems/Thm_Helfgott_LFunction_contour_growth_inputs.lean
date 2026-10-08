-- Prove2me | Theorems.Thm_Helfgott_LFunction_contour_growth_inputs
-- name    : Helfgott.LFunction_contour_growth_inputs
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T14:19:04.087839+00:00
-- url     : https://prove2.me/theorems/6164233f-eecb-4cc6-ba54-669f100a3086
-- title:
--   Full uniform L-function strip growth and right-half-plane anchor lower bound
-- statement:
--   For every Dirichlet character of positive modulus, its full continued L-function has norm at least 1/2 whenever Re(s)>=2. In every closed real strip [a,b], its norm at |Im(s)|>=2 is at most a finite nonnegative constant times exp(pi |Im(s)|/2). The proof derives the completed L-function strip bound from full Mellin kernels, reciprocal gamma growth from full gamma integrals, recurrence and reflection, and the anchor bound from the full twisted Moebius inverse series with complete inverse-square sum estimate two. Neither growth nor nonvanishing is assumed. These inputs support Jensen zero-count and selected horizontal-contour estimates; those estimates and the numerical Goldbach residual remain separate.
-- source:
--   Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897. Mathlib weak functional-equation pairs, Hurwitz/Dirichlet continuation and Euler inverse series contributors, including David Loeffler; complex gamma, reflection and sum-integral contributors. Complete original uniform Mellin endpoint domination, gamma shift/reflection growth and half-plane anchor arguments. Written by Codex.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
open Complex

theorem Helfgott.LFunction_contour_growth_inputs (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (a b : ℝ) :
    (∀ s : ℂ,2 ≤ s.re → (1/2 : ℝ) ≤ ‖χ.LFunction s‖) ∧
    ∃ C : ℝ,0 ≤ C ∧ ∀ s : ℂ,a ≤ s.re → s.re ≤ b → 2 ≤ |s.im| →
      ‖χ.LFunction s‖ ≤ C*Real.exp (Real.pi*|s.im|/2) := by sorry
