-- Prove2me | Theorems.Thm_InfHorizonVP_theorem_3_2_furthermore
-- name    : InfHorizonVP.theorem_3_2_furthermore
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:24.821099+00:00
-- url     : https://prove2.me/theorems/0fa972a5-6bb6-4c46-b6d1-f0e89e9858b2
-- title:
--   Theorem 3.2, 'Furthermore' clause (part 2 of 2; part 1 is theorem_3_2) — Gateaux differentiability of V(t, ·) along x₀ with a measurable normal selector q
-- statement:
--   Let $E$ be a separable real Banach space, assume (H1)–(H4), (H′5), (H6), (H7), and let $x_0\in\mathcal A_{(0,\xi)}$ be optimal for $(P_0)$. Then there is a function $q:\mathbb R_+\to E^*$, measurable from the Lebesgue σ-algebra to $\mathrm{Borel}(E^*,w^*)$, with $q(t)\in N_{\Gamma(t,x_0(t))}(\dot x_0(t))$ for a.e. $t$, such that for a.e. $t\in\mathbb R_+$ the following holds: if $L(t,x_0(t),\cdot)$ is strictly differentiable at $\dot x_0(t)$ with strict derivative $\nabla_yL(t,x_0(t),\dot x_0(t))$, $V(t,\cdot)$ is regular at $x_0(t)$ and $\partial^-_xV(t,x_0(t))=\{w\}$ is a singleton, then $V(t,\cdot)$ is Gateaux differentiable at $x_0(t)$ with Gateaux derivative $\nabla_xV(t,x_0(t))=w$ and
--   $$
--   -\nabla_xV(t,x_0(t))=\nabla_yL(t,x_0(t),\dot x_0(t))+q(t).
--   $$
--
--   This is the "Furthermore" clause of Theorem 3.2; parts (i), (ii) and the "Moreover" clause are the companion item `InfHorizonVP.theorem_3_2`. The paper states this clause without proof (§B.2 proves the other parts).
--
--   **Formalization Note** The clause is read pointwise in $t$, like the "Moreover" clause, and keeps the "Moreover" hypothesis (strict differentiability of $L(t,x_0(t),\cdot)$), without which $\nabla_yL$ is undefined. $V(t,\cdot)$ is finite under (H1)–(H7) (Theorem 3.1); regularity and Gateaux differentiability are stated for its real values.
--
--   Differences from the source:
--   - reading: Furthermore, if V(t, ·) is regular at x0(t) and ∂⁻ₓV(t, x0(t)) is a singleton, then … a.e. t ∈ R+ (after the "Moreover" hypothesis) → for a.e. t, at every t where L(t, x₀(t), ·) is strictly differentiable at ẋ₀(t) with derivative g, V(t, ·) is regular at x₀(t) and ∂⁻ₓV(t, x₀(t)) = {w}, V(t, ·) is Gateaux differentiable at x₀(t) with derivative w and −w = g + q(t); reason: the pointwise reading is the stronger one; the "Moreover" hypothesis is kept because ∇_yL occurs in the conclusion; a Gateaux derivative of the Lipschitz V(t, ·) lies in ∂⁻ₓV(t, x₀(t)), so it is w
--   - reading: q a Borel measurable selector of N_Γ(·,x0(·))(ẋ0(·)) with respect to the weak* topology of E* → q measurable from (ℝ₊, Lebesgue σ-algebra) to borel (WeakDual ℝ E), q(t) ∈ N for a.e. t; reason: the paper's σ-algebra on ℝ₊ is the Lebesgue σ-algebra (p.7) and a selector holds a.e. (p.21), as for the "Borel(E*, w*)-measurable selector" of §A.2
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual with its weak* topology; ẋ the strong derivative → E →L[ℝ] ℝ, identified with WeakDual ℝ E by StrongDual.toWeakDual; deriv x; reason: Lean convention; same objects
--   - encoding: V : ℝ₊ × E → ℝ ∪ {±∞} → EReal-valued valueFn; V(t, ·) as z ↦ (V(t, z)).toReal in regularity and Gateaux differentiability; reason: V is finite under (H1)–(H7) (Theorem 3.1), so toReal changes no value
--   - encoding: L : ℝ₊ × E × E → ℝ ∪ {+∞} → L : ℝ → E → E → ℝ; reason: (H3) makes L finite everywhere
--   - encoding: there exist moduli l₁, l₂ (H3) and γ (H6) → l₁, l₂, γ as arguments with hypotheses HypH3, HypH6, HypH7 on the same functions; reason: a universally quantified hypothesis is equivalent to an existential one
--   - encoding: (H′5) Γ(·, x) lower semicontinuous (definition not restated) → for every open O meeting Γ(t, x), Γ(s, x) meets O for s ∈ ℝ₊ near t; reason: the standard definition of lower semicontinuity of a multifunction
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Theorem 3.2, 'Furthermore' clause, p.10 (PDF p.11)

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
import Definitions.Def_InfHorizonVP_dhSubdiff
import Definitions.Def_InfHorizonVP_clarkeNormalCone
import Definitions.Def_InfHorizonVP_IsStrictlyDifferentiableAt
import Definitions.Def_InfHorizonVP_IsGateauxDifferentiableAt
import Definitions.Def_InfHorizonVP_IsRegularAt
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Theorem 3.2, "Furthermore" clause (part 2 of 2; part 1: `theorem_3_2`) — Gateaux
differentiability of `V(t, ·)` along an optimal trajectory, with a measurable normal selector.**
Frankowska, Sagara, arXiv:1801.00400v3, Theorem 3.2, p.10: "Let x0(·) ∈ 𝒜_(0,ξ) be an optimal
trajectory for (P0). If (H1)–(H4), (H′5), (H6), and (H7) hold, then: … Moreover, if L(t, x0(t), ·)
is strictly differentiable at ẋ0(t), then: … Furthermore, if V(t, ·) is regular at x0(t) and
∂⁻ₓV(t, x0(t)) is a singleton, then V(t, ·) is Gateaux differentiable at x0(t) with:
−∇ₓV(t, x0(t)) = ∇_yL(t, x0(t), ẋ0(t)) + q(t) a.e. t ∈ R+, where q : R+ → E* is a Borel
measurable selector from N_Γ(·,x0(·))(ẋ0(·)) : R+ ⇝ E* with respect to the weak* topology of E*."

**Formalization Note.** There is one `q`, measurable from `(ℝ₊, 𝓛)` (the paper's σ-algebra on ℝ₊,
p.7) to `Borel(E*, w*)` (`borel (WeakDual ℝ E)`, `E*` identified with `WeakDual ℝ E` by
`StrongDual.toWeakDual`), with `q(t) ∈ N_{Γ(t,x₀(t))}(ẋ₀(t))` for a.e. `t` (a selector, p.21). The
clause is read pointwise in `t`, as the "Moreover" clause: for a.e. `t ≥ 0`, at every such `t` where
`L(t, x₀(t), ·)` is strictly differentiable (2.2) at `ẋ₀(t)` with derivative `g` (the "Moreover"
hypothesis, needed for `∇_yL` to exist), `V(t, ·)` is regular at `x₀(t)` and `∂⁻ₓV(t, x₀(t)) = {w}`,
the function `V(t, ·)` is Gateaux differentiable at `x₀(t)` with derivative `w` and `−w = g + q(t)`.
A Gateaux derivative of the Lipschitz `V(t, ·)` lies in `∂⁻ₓV(t, x₀(t))`, so naming it `w` changes
nothing. `V(t, ·)` is real-valued under (H1)–(H7) (Theorem 3.1); regularity and Gateaux
differentiability are stated for `z ↦ (V(t, z)).toReal`. The paper gives no proof of this clause
(§B.2 proves (i), (ii) and the "Moreover"). -/
theorem theorem_3_2_furthermore {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (l₁ l₂ γ : ℝ → ℝ)
    (hH1 : HypH1 Γ) (hH2 : HypH2 L) (hH3 : HypH3 L l₁ l₂) (hH4 : HypH4 Γ)
    (hH5' : HypH5Prime Γ) (hH6 : HypH6 Γ γ) (hH7 : HypH7 l₁ l₂ γ)
    (ξ : E) (x₀ : ℝ → E) (hopt : IsOptimal L Γ 0 ξ x₀) :
    ∃ q : ℝ → E →L[ℝ] ℝ,
      @NullMeasurable ℝ (WeakDual ℝ E) _ (borel (WeakDual ℝ E))
        (fun t => StrongDual.toWeakDual (q t)) (volume.restrict (Ici 0)) ∧
      (∀ᵐ t ∂(volume.restrict (Ici 0)), q t ∈ clarkeNormalCone (Γ t (x₀ t)) (deriv x₀ t)) ∧
      ∀ᵐ t ∂(volume.restrict (Ici 0)), ∀ g w : E →L[ℝ] ℝ,
        IsStrictlyDifferentiableAt (L t (x₀ t)) g (deriv x₀ t) →
        IsRegularAt (fun z => (valueFn L Γ t z).toReal) (x₀ t) →
        dhSubdiff (valueFn L Γ t) (x₀ t) = {w} →
        IsGateauxDifferentiableAt (fun z => (valueFn L Γ t z).toReal) w (x₀ t) ∧
          -w = g + q t := by sorry

end InfHorizonVP
