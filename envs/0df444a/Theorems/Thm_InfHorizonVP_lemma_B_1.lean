-- Prove2me | Theorems.Thm_InfHorizonVP_lemma_B_1
-- name    : InfHorizonVP.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:17:23.356928+00:00
-- url     : https://prove2.me/theorems/2fa8a35c-9e0f-47a1-9234-a367dad506da
-- title:
--   Lemma B.1 (Frankowska [33]) — Filippov-type estimate (corrected: (iii) keeps the ∫d term of (ii))
-- statement:
--   Let $E$ be a separable real Banach space and $0\le t_0\le t_1$. Assume (H4), (H5) and (H6) with modulus $\gamma$. Let $y\in W^{1,1}([t_0,t_1],E)$ with $y(t_0)=\xi$ be such that $t\mapsto d_{\Gamma(t,y(t))}(\dot y(t))$ is integrable on $[t_0,t_1]$. Then for every $\xi'\in E$ and $\varepsilon>0$ there exists $x\in W^{1,1}([t_0,t_1],E)$ such that
--
--   1. $\dot x(t)\in\Gamma(t,x(t))$ for a.e. $t\in[t_0,t_1]$ and $x(t_0)=\xi'$;
--   2. for every $t\in[t_0,t_1]$,
--   $$
--   \|x(t)-y(t)\|\le e^{\int_{t_0}^t\gamma(s)ds}\Bigl(\|\xi-\xi'\|+\int_{t_0}^t d_{\Gamma(s,y(s))}(\dot y(s))\,ds+\varepsilon(t-t_0)\Bigr);
--   $$
--   3. for a.e. $t\in[t_0,t_1]$,
--   $$
--   \|\dot x(t)-\dot y(t)\|\le e^{\int_{t_0}^t\gamma(s)ds}\gamma(t)\Bigl(\|\xi-\xi'\|+\int_{t_0}^t d_{\Gamma(s,y(s))}(\dot y(s))\,ds+\varepsilon(t-t_0)\Bigr)+d_{\Gamma(t,y(t))}(\dot y(t))+\varepsilon .
--   $$
--
--   This is the infinite-dimensional Filippov theorem: an arc that nearly solves the inclusion is close to a true solution. It drives the Lipschitz estimate of Theorem 3.1 and the perturbation Lemma B.2.
--
--   **Formalization Note** $d_C$ is the distance function `Metric.infDist · C`.
--
--   Differences from the source:
--   - correction: (iii) ‖ẋ(t) − ẏ(t)‖ ≤ exp(∫γ) γ(t)(‖ξ − ξ′‖ + ε(t − t0)) + d + ε → the bracket of (ii), with ∫_{t0}^t d_{Γ(s,y(s))}(ẏ(s)) ds, inside γ(t)(…); reason: the printed (iii) is false: E = ℝ, Γ(t, x) = {x}, γ ≡ 2, [t0, t1] = [0, 1], y(t) = t on [0, ½] and ½e^{t−½} on [½, 1], ξ = ξ′ = 0 satisfy every hypothesis; the only solution is x ≡ 0, so the left side is ≥ ½ on (½, 1) while the printed right side is ≤ ε(2e² + 1) < ½ for ε < 0.03
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞) (derivatives and weak* derivatives at t > 0); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual; ẋ the strong derivative → E →L[ℝ] ℝ with the operator norm; deriv x; reason: Lean convention; same objects (deriv agrees with the strong derivative wherever it exists, which is a.e.)
--   - encoding: W^{1,1}([t0, t1], E) → IsArcOn: a.e. differentiable on (t0, t1), integrable deriv, x(s) = x(t0) + ∫_{t0}^s ẋ; reason: the page's definition of the Sobolev space (p.7)
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Lemma B.1, p.24 (PDF p.25)

import Mathlib
import Definitions.Def_InfHorizonVP_IsArcOn
import Definitions.Def_InfHorizonVP_HypH4
import Definitions.Def_InfHorizonVP_HypH5
import Definitions.Def_InfHorizonVP_HypH6
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Lemma B.1 (Frankowska [33]) — Filippov-type estimate (corrected: (iii) keeps the `∫d` term
of (ii)).**
Frankowska, Sagara, arXiv:1801.00400v3, Lemma B.1, p.24: "Let E be a separable Banach space and
[t0, t1] be any closed interval in R+. If (H4), (H5), and (H6) hold, and y(·) ∈ W^{1,1}([t0, t1], E)
is such that t ↦ d_Γ(t,y(t))(ẏ(t)) is integrable with y(t0) = ξ ∈ E, then for every ξ′ ∈ E and
ε > 0 there exists x(·) ∈ W^{1,1}([t0, t1], E) such that: (i) ẋ(t) ∈ Γ(t, x(t)) a.e. t ∈ [t0, t1]
with x(t0) = ξ′; (ii) ‖x(t) − y(t)‖ ≤ exp(∫_{t0}^t γ(s)ds) × (‖ξ − ξ′‖ + ∫_{t0}^t d_Γ(s,y(s))(ẏ(s))ds
+ ε(t − t0)) for every t ∈ [t0, t1]; (iii) ‖ẋ(t) − ẏ(t)‖ ≤ exp(∫_{t0}^t γ(s)ds) γ(t)(‖ξ − ξ′‖ +
ε(t − t0)) + d_Γ(t,y(t))(ẏ(t)) + ε a.e. t ∈ [t0, t1]."

**Formalization Note.** Correction: (iii) as printed is false (take `E = ℝ`, `Γ(t, x) = {x}`,
`γ ≡ 2`, `[t0, t1] = [0, 1]`, `y(t) = t` on `[0, ½]` and `y(t) = ½e^{t−½}` on `[½, 1]`,
`ξ = ξ′ = 0`: the only solution is `x ≡ 0`, so the left side is `≥ ½` on `(½, 1)` while the
printed right side is `≤ ε(2e² + 1)`). Stated with the bracket of (ii), i.e. `γ(t)` times the bound
of (ii) plus `d + ε`, the standard Filippov estimate. `d_C = Metric.infDist · C`; `γ` is the
(H6) modulus. -/
theorem lemma_B_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (Γ : ℝ → E → Set E) (γ : ℝ → ℝ) (hH4 : HypH4 Γ) (hH5 : HypH5 Γ) (hH6 : HypH6 Γ γ)
    (t₀ t₁ : ℝ) (ht₀ : 0 ≤ t₀) (ht : t₀ ≤ t₁) (y : ℝ → E) (hy : IsArcOn y t₀ t₁)
    (hd : IntegrableOn (fun t => Metric.infDist (deriv y t) (Γ t (y t))) (Icc t₀ t₁))
    (ξ : E) (hyξ : y t₀ = ξ) (ξ' : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : ℝ → E, IsArcOn x t₀ t₁ ∧
      (∀ᵐ t ∂(volume.restrict (Icc t₀ t₁)), deriv x t ∈ Γ t (x t)) ∧ x t₀ = ξ' ∧
      (∀ t ∈ Icc t₀ t₁, ‖x t - y t‖ ≤ Real.exp (∫ s in t₀..t, γ s) *
        (‖ξ - ξ'‖ + (∫ s in t₀..t, Metric.infDist (deriv y s) (Γ s (y s))) + ε * (t - t₀))) ∧
      (∀ᵐ t ∂(volume.restrict (Icc t₀ t₁)), ‖deriv x t - deriv y t‖ ≤
        Real.exp (∫ s in t₀..t, γ s) * γ t *
          (‖ξ - ξ'‖ + (∫ s in t₀..t, Metric.infDist (deriv y s) (Γ s (y s))) + ε * (t - t₀)) +
        Metric.infDist (deriv y t) (Γ t (y t)) + ε) := by sorry

end InfHorizonVP
