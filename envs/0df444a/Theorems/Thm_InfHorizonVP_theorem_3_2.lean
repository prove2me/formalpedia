-- Prove2me | Theorems.Thm_InfHorizonVP_theorem_3_2
-- name    : InfHorizonVP.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:25.108747+00:00
-- url     : https://prove2.me/theorems/42eb276e-1a7b-4e94-8fe7-54d56cdafc99
-- title:
--   Theorem 3.2 (i), (ii) and 'Moreover' (part 1 of 2; part 2 is theorem_3_2_furthermore) — Dini–Hadamard subdifferential of V along x₀
-- statement:
--   Let $E$ be a separable real Banach space, assume (H1)–(H4), (H′5), (H6), (H7), and let $x_0\in\mathcal A_{(0,\xi)}$ be optimal for $(P_0)$. Then
--
--   1. for a.e. $t\in\mathbb R_+$ and every $v\in\Gamma(t,x_0(t))$,
--   $$
--   V^-_x(t,x_0(t);\dot x_0(t)-v)\le L(t,x_0(t),v)-L(t,x_0(t),\dot x_0(t));
--   $$
--   2. for a.e. $t\in\mathbb R_+$,
--   $$
--   -\partial^-_xV(t,x_0(t))\subset\partial^\circ_yL(t,x_0(t),\dot x_0(t))+N_{\Gamma(t,x_0(t))}(\dot x_0(t));
--   $$
--   3. (Moreover) for a.e. $t\in\mathbb R_+$: if $L(t,x_0(t),\cdot)$ is strictly differentiable at $\dot x_0(t)$ with strict derivative $\nabla_yL(t,x_0(t),\dot x_0(t))$, then
--   $$
--   -\partial^-_xV(t,x_0(t))\subset\nabla_yL(t,x_0(t),\dot x_0(t))+N_{\Gamma(t,x_0(t))}(\dot x_0(t)).
--   $$
--
--   Here $V^-_x$ and $\partial^-_x$ are the Dini–Hadamard derivative and subdifferential of $V(t,\cdot)$, $\partial^\circ_y$ the Clarke subdifferential of $L(t,x,\cdot)$, and $N$ the Clarke normal cone. This is the paper's first main result; (ii) is the Euler–Lagrange inclusion (ii) of Theorem 4.1. The "Furthermore" clause of Theorem 3.2 (Gateaux differentiability with a measurable normal selector $q$) is the companion item `InfHorizonVP.theorem_3_2_furthermore` (part 2 of 2).
--
--   **Formalization Note** The "Moreover" clause is read pointwise in $t$.
--
--   Differences from the source:
--   - reading: Moreover, if L(t, x0(t), ·) is strictly differentiable at ẋ0(t), then … a.e. t ∈ R+ → for a.e. t, at every t where L(t, x₀(t), ·) is strictly differentiable (2.2) at ẋ₀(t) with derivative g, −∂⁻ₓV ⊆ {g} + N; reason: the pointwise reading is the stronger one and specializes to the global one
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞) (derivatives and weak* derivatives at t > 0); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual; ẋ the strong derivative → E →L[ℝ] ℝ with the operator norm; deriv x; reason: Lean convention; same objects (deriv agrees with the strong derivative wherever it exists, which is a.e.)
--   - encoding: V : ℝ₊ × E → ℝ ∪ {±∞}, inf ∅ = +∞; improper integral as lim_{T→∞} ∫_t^T → EReal-valued valueFn (iInf, ⊤ for the empty family); the improper integral requires integrability on each [t, T] and an EReal limit; reason: Lean convention; integrability makes the finite integrals genuine and holds for every arc under (H2)–(H3)
--   - encoding: L : ℝ₊ × E × E → ℝ ∪ {+∞} → L : ℝ → E → E → ℝ; reason: (H3) bounds |L(t, 0, 0)| and makes L(t, ·, ·) Lipschitz, so L is finite everywhere
--   - encoding: there exist moduli l₁, l₂ (H3) and γ (H6) → l₁, l₂, γ as arguments with hypotheses HypH3, HypH6, HypH7 on the same functions; reason: a universally quantified hypothesis is equivalent to an existential one; the moduli are shared with (H7)
--   - encoding: ∂⁻φ(x̄) defined for x̄ ∈ dom φ → dhSubdiff requires φ(x̄) finite and is empty otherwise; reason: V is finite under (H1)–(H7) (Theorem 3.1), so no instance changes
--   - encoding: (H′5) Γ(·, x) lower semicontinuous (definition not restated) → for every open O meeting Γ(t, x), Γ(s, x) meets O for s ∈ ℝ₊ near t; reason: the standard definition of lower semicontinuity of a multifunction
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Theorem 3.2 (i), (ii) and 'Moreover', p.10 (PDF p.11)

import Mathlib
import Definitions.Def_InfHorizonVP_valueFn
import Definitions.Def_InfHorizonVP_IsOptimal
import Definitions.Def_InfHorizonVP_HypH1
import Definitions.Def_InfHorizonVP_HypH2
import Definitions.Def_InfHorizonVP_HypH3
import Definitions.Def_InfHorizonVP_HypH4
import Definitions.Def_InfHorizonVP_HypH5Prime
import Definitions.Def_InfHorizonVP_HypH6
import Definitions.Def_InfHorizonVP_HypH7
import Definitions.Def_InfHorizonVP_dhLowerDeriv
import Definitions.Def_InfHorizonVP_dhSubdiff
import Definitions.Def_InfHorizonVP_clarkeNormalCone
import Definitions.Def_InfHorizonVP_IsStrictlyDifferentiableAt
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Theorem 3.2 (i), (ii) and the "Moreover" clause (part 1 of 2; part 2:
`theorem_3_2_furthermore`) — upper estimate of the Dini–Hadamard subdifferential of the value
function along an optimal trajectory.**
Frankowska, Sagara, arXiv:1801.00400v3, Theorem 3.2, p.10: "Let x0(·) ∈ 𝒜_(0,ξ) be an optimal
trajectory for (P0). If (H1)–(H4), (H′5), (H6), and (H7) hold, then: (i) V⁻ₓ(t, x0(t); ẋ0(t) − v) ≤
L(t, x0(t), v) − L(t, x0(t), ẋ0(t)) a.e. t ∈ R+ for every v ∈ Γ(t, x0(t)); (ii) −∂⁻ₓV(t, x0(t)) ⊂
∂°_yL(t, x0(t), ẋ0(t)) + N_Γ(t,x0(t))(ẋ0(t)) a.e. t ∈ R+. Moreover, if L(t, x0(t), ·) is strictly
differentiable at ẋ0(t), then: −∂⁻ₓV(t, x0(t)) ⊂ ∇_yL(t, x0(t), ẋ0(t)) + N_Γ(t,x0(t))(ẋ0(t)) a.e.
t ∈ R+."

**Formalization Note.** `V⁻ₓ(t, x; w)` is `dhLowerDeriv (V t) x w`, `∂⁻ₓV(t, x)` is
`dhSubdiff (V t) x`, `∂°_yL(t, x, y)` is `clarkeGrad (L t x) y`, sets are added pointwise. In (i)
one null set serves all `v`, as printed. The "Moreover" clause is read pointwise: for a.e. `t`, at
every such `t` where `L(t, x₀(t), ·)` is strictly differentiable (2.2) at `ẋ₀(t)` with derivative
`g`, the inclusion with `{g}` holds. -/
theorem theorem_3_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (l₁ l₂ γ : ℝ → ℝ)
    (hH1 : HypH1 Γ) (hH2 : HypH2 L) (hH3 : HypH3 L l₁ l₂) (hH4 : HypH4 Γ)
    (hH5' : HypH5Prime Γ) (hH6 : HypH6 Γ γ) (hH7 : HypH7 l₁ l₂ γ)
    (ξ : E) (x₀ : ℝ → E) (hopt : IsOptimal L Γ 0 ξ x₀) :
    (∀ᵐ t ∂(volume.restrict (Ici 0)), ∀ v ∈ Γ t (x₀ t),
      dhLowerDeriv (valueFn L Γ t) (x₀ t) (deriv x₀ t - v) ≤
        ((L t (x₀ t) v - L t (x₀ t) (deriv x₀ t) : ℝ) : EReal)) ∧
    (∀ᵐ t ∂(volume.restrict (Ici 0)),
      -dhSubdiff (valueFn L Γ t) (x₀ t) ⊆
        QuasiHemiVI.Existence.clarkeGrad (L t (x₀ t)) (deriv x₀ t) +
          clarkeNormalCone (Γ t (x₀ t)) (deriv x₀ t)) ∧
    (∀ᵐ t ∂(volume.restrict (Ici 0)), ∀ g : E →L[ℝ] ℝ,
      IsStrictlyDifferentiableAt (L t (x₀ t)) g (deriv x₀ t) →
      -dhSubdiff (valueFn L Γ t) (x₀ t) ⊆ {g} + clarkeNormalCone (Γ t (x₀ t)) (deriv x₀ t)) := by sorry

end InfHorizonVP
