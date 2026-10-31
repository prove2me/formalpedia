-- Prove2me | Theorems.Thm_InfHorizonVP_theorem_4_1
-- name    : InfHorizonVP.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:20:25.456721+00:00
-- url     : https://prove2.me/theorems/e9e9326f-5ac4-472e-b334-a428276bec8a
-- title:
--   Theorem 4.1 — Euler–Lagrange inclusion, maximum principle and p(t) → 0 under interiority (H8)
-- statement:
--   Let $E$ be a separable real Banach space and assume (H1)–(H4), (H′5), (H6), (H7). Let $x_0\in\mathcal A_{(0,\xi)}$ be optimal for $(P_0)$ and satisfy (H8). Suppose $\partial^-_xV(0,x_0(0))\neq\emptyset$ and $\partial^+_xL(t,x_0(t),\dot x_0(t))\neq\emptyset$ for a.e. $t\in\mathbb R_+$. Then:
--
--   **(a)** $\partial^-_xV(t,x_0(t))\neq\emptyset$ for every $t\in\mathbb R_+$.
--
--   **(b)** For every $x^*\in\partial^-_xV(0,x_0(0))$ and every weakly$^*$ scalarly measurable $f:\mathbb R_+\to E^*$ with $f(t)\in\partial^+_xL(t,x_0(t),\dot x_0(t))$ for a.e. $t$, the Gelfand integral $\int_0^tf(s)\,ds$ exists for every $t\ge0$, and the function
--   $$
--   p(t)=\int_0^tf(s)\,ds-x^*
--   $$
--   is locally absolutely continuous and satisfies
--
--   1. $-p(t)\in\partial^-_xV(t,x_0(t))$ for every $t\in\mathbb R_+$;
--   2. $p(t)\in\partial^\circ_yL(t,x_0(t),\dot x_0(t))+N_{\Gamma(t,x_0(t))}(\dot x_0(t))$ for a.e. $t$;
--   3. $p$ has a weak$^*$ derivative $\dot p(t)\in\partial^+_xL(t,x_0(t),\dot x_0(t))$ for a.e. $t$;
--   4. $H(t,x_0(t),p(t))=\langle p(t),\dot x_0(t)\rangle-L(t,x_0(t),\dot x_0(t))$ for a.e. $t$;
--   5. $\displaystyle\lim_{t\to\infty}p(t)=0$ in $E^*$.
--
--   This is the paper's main result: a nonconvex, nonsmooth Pontryagin-type necessary condition for infinite horizon problems in Banach spaces, with the adjoint arc tied to the value function by (i) and the transversality condition at infinity (v) derived rather than assumed.
--
--   Differences from the source:
--   - reading: the locally absolutely continuous function p : R+ → E* defined by p(t) := ∫_0^t f(s)ds − x* as a Gelfand integral → the Gelfand integral of f over [0, t] exists for every t ≥ 0, and every p with p(t) + x* = ∫_0^t f (all t ≥ 0) is locally absolutely continuous and satisfies (i)–(v); reason: existence and local absolute continuity of p are part of the claim (proved on p.31), not hypotheses
--   - reading: In particular, if ∂⁻ₓV(0, x0(0)) is nonempty, then ∂⁻ₓV(t, x0(t)) is nonempty for every t → conclusion (a), under all hypotheses of the theorem; reason: 'in particular' marks a consequence of what precedes; the proof needs a selector of ∂⁺ₓL
--   - reading: (iv) … − L(t, x0(t)), ẋ0(t)) → − L(t, x₀(t), ẋ₀(t)); reason: stray parenthesis on the page
--   - encoding: ṗ(t) the weak* derivative, (iii) a.e. t ∈ R+ → ∃ y, HasWeakStarDerivAt p y t ∧ y ∈ ∂⁺ₓL, for a.e. t > 0; reason: the weak* derivative is defined at t > 0 (p.11)
--   - encoding: locally absolutely continuous p → ∀ τ > 0, AbsolutelyContinuousOnInterval p 0 τ (dual norm); reason: Mathlib's definition is the page's (p.11)
--   - encoding: H : R+ × E × E* → R ∪ {+∞} → EReal-valued hamiltonian (supremum in EReal); reason: Lean convention; same values
--   - encoding: functions on ℝ₊ = [0, ∞) → functions on ℝ with every condition restricted to [0, ∞) (derivatives and weak* derivatives at t > 0); reason: Lean convention; values at negative times are never used, same instances
--   - encoding: E* the norm dual; ẋ the strong derivative → E →L[ℝ] ℝ with the operator norm; deriv x; reason: Lean convention; same objects (deriv agrees with the strong derivative wherever it exists, which is a.e.)
--   - encoding: V : ℝ₊ × E → ℝ ∪ {±∞}, inf ∅ = +∞; improper integral as lim_{T→∞} ∫_t^T → EReal-valued valueFn (iInf, ⊤ for the empty family); the improper integral requires integrability on each [t, T] and an EReal limit; reason: Lean convention; integrability makes the finite integrals genuine and holds for every arc under (H2)–(H3)
--   - encoding: L : ℝ₊ × E × E → ℝ ∪ {+∞} → L : ℝ → E → E → ℝ; reason: (H3) bounds |L(t, 0, 0)| and makes L(t, ·, ·) Lipschitz, so L is finite everywhere
--   - encoding: there exist moduli l₁, l₂ (H3) and γ (H6) → l₁, l₂, γ as arguments with hypotheses HypH3, HypH6, HypH7 on the same functions; reason: a universally quantified hypothesis is equivalent to an existential one; the moduli are shared with (H7)
--   - encoding: ∂⁻φ(x̄) defined for x̄ ∈ dom φ → dhSubdiff requires φ(x̄) finite and is empty otherwise; reason: V is finite under (H1)–(H7) (Theorem 3.1), so no instance changes
--   - encoding: (H′5) Γ(·, x) lower semicontinuous (definition not restated) → for every open O meeting Γ(t, x), Γ(s, x) meets O for s ∈ ℝ₊ near t; reason: the standard definition of lower semicontinuity of a multifunction
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, Theorem 4.1, p.12 (PDF p.13)

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
import Definitions.Def_InfHorizonVP_HypH8
import Definitions.Def_InfHorizonVP_dhSubdiff
import Definitions.Def_InfHorizonVP_dhSuperdiff
import Definitions.Def_InfHorizonVP_clarkeNormalCone
import Definitions.Def_InfHorizonVP_hamiltonian
import Definitions.Def_InfHorizonVP_HasWeakStarDerivAt
import Definitions.Def_InfHorizonVP_IsWeakStarScalarlyMeasurable
import Definitions.Def_InfHorizonVP_IsGelfandIntegral
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Theorem 4.1 — Euler–Lagrange inclusion, maximum principle and transversality at infinity
under the interiority condition (H8).**
Frankowska, Sagara, arXiv:1801.00400v3, Theorem 4.1, p.12: "Suppose that (H1)–(H4), (H′5), (H6),
(H7), and (H8) hold. If ∂⁻ₓV(0, x0(0)) is nonempty and ∂⁺ₓL(t, x0(t), ẋ0(t)) is nonempty a.e.
t ∈ R+, then for every x* ∈ ∂⁻ₓV(0, x0(0)) and weakly* scalarly measurable selector f : R+ → E*
from the Dini–Hadamard superdifferential mapping ∂⁺ₓL(·, x0(·), ẋ0(·)) : R+ ⇝ E*, the locally
absolutely continuous function p : R+ → E* defined by p(t) := ∫_0^t f(s)ds − x* as a Gelfand
integral satisfies: (i) −p(t) ∈ ∂⁻ₓV(t, x0(t)) for every t ∈ R+; (ii) p(t) ∈ ∂°_yL(t, x0(t), ẋ0(t))
+ N_Γ(t,x0(t))(ẋ0(t)) a.e. t ∈ R+; (iii) ṗ(t) ∈ ∂⁺ₓL(t, x0(t), ẋ0(t)) a.e. t ∈ R+; (iv)
H(t, x0(t), p(t)) = ⟨p(t), ẋ0(t)⟩ − L(t, x0(t)), ẋ0(t)) a.e. t ∈ R+; (v) lim_{t→∞} p(t) = 0, where
ṗ(t) denotes the weak* derivative of p(·) at t ∈ R+. In particular, if ∂⁻ₓV(0, x0(0)) is
nonempty, then ∂⁻ₓV(t, x0(t)) is nonempty for every t ∈ R+." Here x0 ∈ 𝒜_(0,ξ) is an optimal
trajectory for (P0) (p.11, (H8)).

**Formalization Note.** The conclusion has two parts. (a) The "In particular": `∂⁻ₓV(t, x₀(t)) ≠ ∅`
for every `t ≥ 0`. (b) For every `x*` and every selector `f`: the Gelfand integral `∫_0^t f` exists
for every `t ≥ 0` (so `p` is well defined), and every `p` with `p(t) + x* = ∫_0^t f` for all
`t ≥ 0` is locally absolutely continuous on `ℝ₊` and satisfies (i)–(v). In (iii), `p` has a weak\*
derivative at a.e. `t > 0`, lying in `∂⁺ₓL`. (iv) reads `L(t, x₀(t), ẋ₀(t))` (the page has a stray
parenthesis). (v) is convergence in the dual norm. `E* = E →L[ℝ] ℝ`; `ẋ₀ = deriv x₀`; `V` and `H`
are `EReal`-valued. -/
theorem theorem_4_1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (L : ℝ → E → E → ℝ) (Γ : ℝ → E → Set E) (l₁ l₂ γ : ℝ → ℝ)
    (hH1 : HypH1 Γ) (hH2 : HypH2 L) (hH3 : HypH3 L l₁ l₂) (hH4 : HypH4 Γ)
    (hH5' : HypH5Prime Γ) (hH6 : HypH6 Γ γ) (hH7 : HypH7 l₁ l₂ γ)
    (ξ : E) (x₀ : ℝ → E) (hopt : IsOptimal L Γ 0 ξ x₀) (hH8 : HypH8 Γ x₀)
    (hV : (dhSubdiff (valueFn L Γ 0) (x₀ 0)).Nonempty)
    (hL : ∀ᵐ t ∂(volume.restrict (Ici 0)),
      (dhSuperdiff (fun z => ((L t z (deriv x₀ t) : ℝ) : EReal)) (x₀ t)).Nonempty) :
    (∀ t, 0 ≤ t → (dhSubdiff (valueFn L Γ t) (x₀ t)).Nonempty) ∧
    ∀ xstar ∈ dhSubdiff (valueFn L Γ 0) (x₀ 0), ∀ f : ℝ → E →L[ℝ] ℝ,
      IsWeakStarScalarlyMeasurable f (Ici 0) →
      (∀ᵐ t ∂(volume.restrict (Ici 0)),
        f t ∈ dhSuperdiff (fun z => ((L t z (deriv x₀ t) : ℝ) : EReal)) (x₀ t)) →
      (∀ t, 0 ≤ t → ∃ z : E →L[ℝ] ℝ, IsGelfandIntegral f (Icc 0 t) z) ∧
      ∀ p : ℝ → E →L[ℝ] ℝ, (∀ t, 0 ≤ t → IsGelfandIntegral f (Icc 0 t) (p t + xstar)) →
        (∀ τ, 0 < τ → AbsolutelyContinuousOnInterval p 0 τ) ∧
        (∀ t, 0 ≤ t → -p t ∈ dhSubdiff (valueFn L Γ t) (x₀ t)) ∧
        (∀ᵐ t ∂(volume.restrict (Ici 0)),
          p t ∈ QuasiHemiVI.Existence.clarkeGrad (L t (x₀ t)) (deriv x₀ t) +
            clarkeNormalCone (Γ t (x₀ t)) (deriv x₀ t)) ∧
        (∀ᵐ t ∂(volume.restrict (Ioi 0)), ∃ y : E →L[ℝ] ℝ, HasWeakStarDerivAt p y t ∧
          y ∈ dhSuperdiff (fun z => ((L t z (deriv x₀ t) : ℝ) : EReal)) (x₀ t)) ∧
        (∀ᵐ t ∂(volume.restrict (Ici 0)),
          hamiltonian L Γ t (x₀ t) (p t) =
            ((p t (deriv x₀ t) - L t (x₀ t) (deriv x₀ t) : ℝ) : EReal)) ∧
        Tendsto p atTop (𝓝 0) := by sorry

end InfHorizonVP
