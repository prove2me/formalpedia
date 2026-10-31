-- Prove2me | Theorems.Thm_InfHorizonVP_lemma_B_2
-- name    : InfHorizonVP.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:24.489704+00:00
-- url     : https://prove2.me/theorems/cb8bbf93-9874-4c54-a816-b29a24ac9eea
-- title:
--   Lemma B.2 — arcs through v ending at x₀(t + h) with o(h) errors
-- statement:
--   Let $E$ be a separable real Banach space and assume (H4), (H′5) and (H6) with modulus $\gamma$. Let $x_0:\mathbb R_+\to E$, let $t\ge0$ be such that $x_0$ has derivative $\dot x_0(t)$ at $t$ (from the right), and let $v\in\Gamma(t,x_0(t))$. Then there are arcs $x_h\in W^{1,1}([t,t+h],E)$, $h>0$, such that
--
--   1. $\dot x_h(s)\in\Gamma(s,x_h(s))$ for a.e. $s\in[t,t+h]$ and $x_h(t+h)=x_0(t+h)$;
--   2. $\|x_h(t)-x_0(t)-h(\dot x_0(t)-v)\|=o(h)$ as $h\downarrow0$;
--   3. $\|\dot x_h-v\|_{L^1([t,t+h])}=o(h)$ as $h\downarrow0$.
--
--   The arcs $x_h$ follow the velocity $v$ and rejoin $x_0$; comparing their cost with that of $x_0$ gives the subdifferential estimate (i) of Theorem 3.2.
--
--   **Formalization Note** "$=o(h)$" means $h^{-1}(\cdot)\to0$ as $h\downarrow0$.
--
--   Differences from the source:
--   - generalization: x0 the optimal trajectory of Theorem 3.2, with a strong derivative ẋ0(t) at t → any x₀ : ℝ → E with a right derivative at t (HasDerivWithinAt on [t, ∞)); reason: the proof uses only x₀(t), x₀(t + h) and this derivative; the optimal trajectory with a strong derivative at t is an instance
--   - encoding: o(h) → h⁻¹ · (…) → 0 as h ↓ 0 (along 𝓝[>] 0); reason: the page's Landau symbol (p.26)
--   - encoding: ‖ẋh(·) − v‖_{L¹([t,t+h])} → ∫_t^{t+h} ‖deriv (xh h) s − v‖ ds; reason: the integrand is integrable since x_h is an arc
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞) (derivatives and weak* derivatives at t > 0); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual; ẋ the strong derivative → E →L[ℝ] ℝ with the operator norm; deriv x; reason: Lean convention; same objects (deriv agrees with the strong derivative wherever it exists, which is a.e.)
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Lemma B.2, p.26 (PDF p.27)

import Mathlib
import Definitions.Def_InfHorizonVP_IsArcOn
import Definitions.Def_InfHorizonVP_HypH4
import Definitions.Def_InfHorizonVP_HypH5Prime
import Definitions.Def_InfHorizonVP_HypH6
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Lemma B.2 — arcs through `v` ending on `x₀`, with `o(h)` errors.**
Frankowska, Sagara, arXiv:1801.00400v3, Lemma B.2, p.26: "Suppose that (H4), (H′5), and (H6) hold.
Let t ∈ R+ be such that the strong derivative ẋ0(t) exists and v ∈ Γ(t, x0(t)) be arbitrarily
fixed. Then for every h > 0 there exists xh(·) ∈ W^{1,1}([t, t + h], E) such that: (i) ẋh(s) ∈
Γ(s, xh(s)) a.e. s ∈ [t, t + h] with xh(t + h) = x0(t + h); (ii) ‖xh(t) − x0(t) − h(ẋ0(t) − v)‖ =
o(h); (iii) ‖ẋh(·) − v‖_{L¹([t,t+h])} = o(h)." Here (p.26) "Denote by o(h) > 0 the Landau symbol with
lim_{h↓0} h⁻¹o(h) = 0."

**Formalization Note.** The family `(x_h)_{h>0}` is `xh : ℝ → ℝ → E`; "`= o(h)`" is
`h⁻¹ · (…) → 0` as `h ↓ 0`. The `L¹` norm is `∫_t^{t+h} ‖ẋ_h(s) − v‖ ds` (integrable since `x_h` is
an arc). `x₀` is any function with derivative `ẋ₀(t)` at `t` from the right (generalization: the
lemma's `x₀` is the optimal trajectory, the proof uses only `x₀(t)`, `x₀(t + h)` and this
derivative, and a two-sided strong derivative is in particular a right derivative). -/
theorem lemma_B_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (Γ : ℝ → E → Set E) (γ : ℝ → ℝ) (hH4 : HypH4 Γ) (hH5' : HypH5Prime Γ) (hH6 : HypH6 Γ γ)
    (x₀ : ℝ → E) (t : ℝ) (ht : 0 ≤ t) (dx₀ : E) (hder : HasDerivWithinAt x₀ dx₀ (Ici t) t)
    (v : E) (hv : v ∈ Γ t (x₀ t)) :
    ∃ xh : ℝ → ℝ → E,
      (∀ h, 0 < h → IsArcOn (xh h) t (t + h) ∧
        (∀ᵐ s ∂(volume.restrict (Icc t (t + h))), deriv (xh h) s ∈ Γ s (xh h s)) ∧
        xh h (t + h) = x₀ (t + h)) ∧
      Tendsto (fun h => h⁻¹ * ‖xh h t - x₀ t - h • (dx₀ - v)‖) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun h => h⁻¹ * ∫ s in t..(t + h), ‖deriv (xh h) s - v‖) (𝓝[>] 0) (𝓝 0) := by sorry

end InfHorizonVP
