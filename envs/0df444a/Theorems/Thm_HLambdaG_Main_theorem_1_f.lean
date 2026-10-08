-- Prove2me | Theorems.Thm_HLambdaG_Main_theorem_1_f
-- name    : HLambdaG.Main.theorem_1_f
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:45:28.254904+00:00
-- url     : https://prove2.me/theorems/5db88a09-3633-4a13-a84d-6b070a570ff8
-- title:
--   Theorem 1(f), p. 639 — H converges iff G converges, and H = λG
-- statement:
--   Let $F$ be a cumulative input with marginal averages $G$ and $H$. Let $T_1$ and $T_2$ be separate time changes, each satisfying $T_i(s)/s\to\lambda^{-1}$ for the same $\lambda>0$. Assume approximation condition (14) for $T_1$ and condition (15) for $T_2$. Then $H(t)$ has a finite real limit as $t\to\infty$ if and only if $G(s)$ has a finite real limit as $s\to\infty$. Whenever $H(t)\to h$ and $G(s)\to g$,
--
--   $$
--   h=\lambda g.
--   $$
--
--   This is the paper's two-way sample-path version of the $H=\lambda G$ relation. Its conclusion includes the identification of the limits, as well as their simultaneous existence.
--
--   **Formalization Note** The two time changes share the same positive $\lambda$ but may be different. The limits in this part are finite real limits; Theorem 1(c) handles possibly infinite lim inf and lim sup. No inverse-rate conclusion or asymptotic bound is assumed as an extra hypothesis.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 639, Theorem 1(f), https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main

open Filter Topology

/-- Theorem 1(f), p. 639: finite limits coexist and satisfy H = λG. -/
theorem theorem_1_f
    (C : CumulativeInput) (τ₁ τ₂ : TimeChange) (lam : ℝ) (hlam : 0 < lam)
    (hT₁ : Tendsto (fun s : ℝ≥0 => (τ₁.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h14 : Cond14 C τ₁)
    (hT₂ : Tendsto (fun s : ℝ≥0 => (τ₂.T s : ℝ) / (s : ℝ)) atTop (𝓝 lam⁻¹))
    (h15 : Cond15 C τ₂) :
    ((∃ h : ℝ, Tendsto (H C) atTop (𝓝 h)) ↔
      (∃ g : ℝ, Tendsto (G C) atTop (𝓝 g))) ∧
      ∀ h g : ℝ, Tendsto (H C) atTop (𝓝 h) →
        Tendsto (G C) atTop (𝓝 g) → h = lam * g := by sorry

end HLambdaG.Main
