-- Prove2me | Theorems.Thm_HLambdaG_Main_lemma_1
-- name    : HLambdaG.Main.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:43:10.782379+00:00
-- url     : https://prove2.me/theorems/8ced8f6e-3433-4d1b-bd0c-74d00a96969b
-- title:
--   Lemma 1, p. 638 — reciprocal asymptotic rates of a time change and its inverse
-- statement:
--   Let $T$ be a finite, nonnegative, nondecreasing, right-continuous time change on $[0,\infty)$ with $T(s)\to\infty$, and let $S(t)=\inf\{s\geq0:T(s)>t\}$. For every fixed $\lambda>0$,
--
--   $$
--   \frac{S(t)}{t}\longrightarrow\lambda\quad(t\to\infty)
--   \quad\Longleftrightarrow\quad
--   \frac{T(s)}{s}\longrightarrow\lambda^{-1}\quad(s\to\infty).
--   $$
--
--   This inversion principle translates a growth rate between the customer and time scales used in the main theorem.
--
--   **Formalization Note** The ratios are real-valued. Their values at zero are irrelevant to limits at infinity.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 638, Lemma 1, https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main

open Filter Topology

/-- Lemma 1, p. 638: reciprocal asymptotic rates for a time change and its inverse. -/
theorem lemma_1 (τ : TimeChange) (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun t : ℝ≥0 => (inv τ t : ℝ) / (t : ℝ)) atTop (𝓝 lam) ↔
      Tendsto (fun s : ℝ≥0 => (τ.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹) := by sorry

end HLambdaG.Main
