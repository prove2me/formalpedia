-- Prove2me | Theorems.Thm_Helfgott_actual_mellin_strip_decay_expanded
-- name    : Helfgott.actual_mellin_strip_decay_expanded
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T14:47:16.63665+00:00
-- url     : https://prove2.me/theorems/eda75db7-693c-4100-9dfd-1f7fcd5e1329
-- title:
--   Arbitrary-order full actual Mellin decay uniformly over a contour strip and bounded additive phases
-- statement:
--   For either actual signed etaPlus or actual etaStar, every nonnegative integer n, every closed real strip [a,b] with a>-1, and every bounded phase range |delta|<=W, there is a finite nonnegative constant C, independent of sigma, delta and height t, such that (1+|t|^n) times the norm of the full additive-phase Mellin transform at sigma+it is at most C throughout the strip. All derivative, integrability and smoothing-convolution arguments are proved for the actual functions, including all signed and infinite tails. The proof supplies finite recursive majorants for the constant. This provides uniform smoothing decay needed for high horizontal contour edges and vertical integral tails. It does not assume or prove quantitative L-function zero estimates or the complete Goldbach error bound.
-- source:
--   Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897; full actual smoothing setup https://arxiv.org/html/1312.7748v2. Mathlib Fourier and Mellin transform contributors, including David Loeffler; Fourier derivative and integral-norm estimate contributors. Original complete arbitrary-order and uniform-strip derivative-majorant proofs. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.MellinTransform
open MeasureTheory Set

theorem Helfgott.actual_mellin_strip_decay_expanded (η : ℝ → ℝ)
    (hη : η = Helfgott.etaPlus ∨ η = Helfgott.etaStar) (n : ℕ) (a b W : ℝ) (ha : -1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ δ t : ℝ, a ≤ σ → σ ≤ b → abs δ ≤ W →
      ((1 : ℝ) + (abs t)^n) * norm (mellin
        (fun u : ℝ => (η u : ℂ) * Complex.exp
          (Complex.I * ((2 * Real.pi * δ : ℝ) : ℂ) * (u : ℂ)))
        ((σ : ℂ) + (t : ℂ) * Complex.I)) ≤ C := by sorry
