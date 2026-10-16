-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_phase_increment_inv
-- name    : OAI.ShortEgyptian.phase_increment_inv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:18:39.58767+00:00
-- url     : https://prove2.me/theorems/989d00c1-4b8c-4523-bb4d-218b75818fd3
-- title:
--   Inverse of $e(x)-1$: $\,(e^{2\pi i x}-1)^{-1}=-\tfrac12-\tfrac{i}{2}\cot(\pi x)$ for $0<x<1$
-- statement:
--   Write $e(x)=\exp(2\pi i x)$ for $x\in\mathbb{R}$. For every real number $x$ with $0<x<1$,
--
--   $$
--   \big(e(x)-1\big)^{-1}=-\frac12-\frac{\cos(\pi x)}{2\sin(\pi x)}\,i .
--   $$
--
--   In particular $e(x)\ne1$ for $0<x<1$, the real part of $(e(x)-1)^{-1}$ is the constant $-\tfrac12$, and its imaginary part is $-\tfrac12\cot(\pi x)$, an increasing function of $x$ on $(0,1)$. These facts drive the summation-by-parts proof of the Kusmin–Landau-type estimate for exponential sums $\sum_n e(f(n))$ whose phase increments are monotone and stay away from the integers.
--
--   **Formalization Note** The function $e$ is `phase`, defined as `Complex.exp` of the real number $2\pi x$, cast to $\mathbb{C}$, times `Complex.I`. The inverse is the complex inverse, for which Lean sets $0^{-1}=0$; the identity shows that this convention is never invoked here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/FirstDerivative.lean#L60-L86

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.phase_increment_inv {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (phase x - 1)⁻¹ = (-1 / 2 : ℂ) -
      (↑(Real.cos (Real.pi * x) / (2 * Real.sin (Real.pi * x))) : ℂ) * Complex.I := by sorry
