-- Prove2me | Theorems.Thm_HLambdaG_Main_theorem_1_c
-- name    : HLambdaG.Main.theorem_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:45:39.191401+00:00
-- url     : https://prove2.me/theorems/f3ff8272-f4cb-445d-be02-b1d0f90501d9
-- title:
--   Theorem 1(c), p. 639 — equality of asymptotic bounds
-- statement:
--   Let $F$ be a cumulative input with marginal averages $G$ and $H$. Let $T_1$ and $T_2$ be separate time changes, each satisfying $T_i(s)/s\to\lambda^{-1}$ for the same $\lambda>0$. Assume (14) for $T_1$ and (15) for $T_2$. Then
--
--   $$
--   \liminf_{t\to\infty}H(t)=\liminf_{s\to\infty}\lambda G(s),
--   \qquad
--   \limsup_{t\to\infty}H(t)=\limsup_{s\to\infty}\lambda G(s).
--   $$
--
--   This identifies both lower and upper asymptotic behavior, even when the averages do not converge.
--
--   **Formalization Note** The limits are extended-real lim inf and lim sup. The two time changes need not agree. This part is true as printed despite the swapped one-sided bounds in parts (a) and (b).
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 639, Theorem 1(c), https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main

open Filter Topology

/-- Theorem 1(c), p. 639: equality of both extended-real asymptotic bounds. -/
theorem theorem_1_c
    (C : CumulativeInput) (τ₁ τ₂ : TimeChange) (lam : ℝ) (hlam : 0 < lam)
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h14 : Cond14 C τ₁)
    (hT₂ : Tendsto (fun s : ℝ≥0 => (τ₂.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h15 : Cond15 C τ₂) :
    liminfE (H C) = liminfE (fun s => lam * G C s) ∧
      limsupE (H C) = limsupE (fun s => lam * G C s) := by sorry

end HLambdaG.Main
