-- Prove2me | Theorems.Thm_MarkovSA_theorem_2_1
-- name    : MarkovSA.theorem_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:32.113216+00:00
-- url     : https://prove2.me/theorems/f9676510-614c-4389-9b81-15f930f8e412
-- title:
--   Theorem 2.1 — finite-sample mean-square bounds for Markovian stochastic approximation (corrected: $\mathcal Y$ has at least two points)
-- statement:
--   Let $\mathcal Y$ be a finite set with at least two points, $P$ a transition matrix with stationary distribution $\mu$ satisfying Assumption 2.3, and consider the iterates $x_k$ of Algorithm (6),
--
--   $$
--   x_{k+1}=x_k+\alpha_k\big(F(x_k,Y_k)-x_k+w_k\big),
--   $$
--
--   on a finite-dimensional real space with norm $\|\cdot\|_c$, under Assumptions 2.1, 2.2 and 2.4 (the chain being Markov relative to a filtration to which the iterates are adapted). Let $A=A_1+A_2+1$, $B=B_1+B_2$, $c_1=(\|x_0-x^*\|_c+\|x_0\|_c+B/A)^2$, $c_2=(A\|x^*\|_c+B)^2$, let $\varphi_1,\varphi_2,\varphi_3$ be the constants (16) of any admissible smoothing data, $T=\min(\varphi_2/(\varphi_3A^2),1/(4A))$, $t_\delta$ the mixing time and $t_k=t_{\alpha_k}$. Then:
--
--   1. **Thresholds (Condition 2.1).** There is $\bar\alpha\in(0,1)$ with $\alpha t_\alpha\le T$ for all $\alpha\in(0,\bar\alpha)$; for every $\alpha>0$ there is $\bar h$ above which $(\alpha,h)$ is admissible for $\alpha/(k+h)$; and the same for $\alpha/(k+h)^\xi$, $\xi\in(0,1)$.
--   2. **Constant stepsize** $\alpha_k\equiv\alpha\in(0,\bar\alpha)$, for any such $\bar\alpha$: $\|x_k-x^*\|_c^2\le c_1$ a.s. for $k<t_\alpha$, and for $k\ge t_\alpha$
--   $$
--   \mathbb E\|x_k-x^*\|_c^2\le\varphi_1c_1(1-\varphi_2\alpha)^{k-t_\alpha}+\frac{\varphi_3c_2}{\varphi_2}\alpha t_\alpha.
--   $$
--   3. **Linear stepsize** $\alpha_k=\alpha/(k+h)$, $(\alpha,h)$ admissible, $K$ the least $K_0$ with $t_k\le k$ for $k\ge K_0$: $\|x_k-x^*\|_c^2\le c_1$ a.s. for $k<K$, and for $k\ge K$
--   $$
--   \mathbb E\|x_k-x^*\|_c^2\le\begin{cases}\varphi_1c_1\big(\frac{K+h}{k+h}\big)^{\varphi_2\alpha}+\frac{8\alpha^2\varphi_3c_2}{1-\varphi_2\alpha}\frac{t_k}{(k+h)^{\varphi_2\alpha}}, & \alpha<1/\varphi_2,\\[2pt] \varphi_1c_1\frac{K+h}{k+h}+8\alpha^2\varphi_3c_2\frac{t_k\log(k+h)}{k+h}, & \alpha=1/\varphi_2,\\[2pt] \varphi_1c_1\big(\frac{K+h}{k+h}\big)^{\varphi_2\alpha}+\frac{8e\alpha^2\varphi_3c_2}{\varphi_2\alpha-1}\frac{t_k}{k+h}, & \alpha>1/\varphi_2.\end{cases}
--   $$
--   4. **Polynomial stepsize** $\alpha_k=\alpha/(k+h)^\xi$, $\xi\in(0,1)$, $(\alpha,h)$ admissible: $\|x_k-x^*\|_c^2\le c_1$ a.s. for $k<K$, and for $k\ge K$
--   $$
--   \mathbb E\|x_k-x^*\|_c^2\le\varphi_1c_1\exp\Big(-\frac{\varphi_2\alpha}{1-\xi}\big((k+h)^{1-\xi}-(K+h)^{1-\xi}\big)\Big)+\frac{4\varphi_3c_2\alpha}{\varphi_2}\frac{t_k}{(k+h)^\xi}.
--   $$
--
--   Here $(\alpha,h)$ is admissible if Condition A.1 holds, $t_k\ge1$, $\alpha_{k-t_k}\le2\alpha_k$ for $k\ge t_k$, and $h\ge[2\xi/(\varphi_2\alpha)]^{1/(1-\xi)}$ when $\xi<1$.
--
--   The bounds split into a bias term, driven by the initial error $c_1$, and a variance term, driven by the noise level $c_2$ at $x^*$ and the mixing time. They are the engine behind the paper's finite-sample results for Q-learning, V-trace, $n$-step TD and TD($\lambda$).
--
--   **Formalization Note** $e$ is $\exp(1)$; powers with real exponents use a positive base.
--
--   Differences from the source:
--   - correction: $\mathcal Y$ any finite set → $\mathcal Y$ has at least two points; reason: with one point $t_\delta=0$ for every $\delta$; counterexample: $\mathcal Y=\{y\}$, $F\equiv0$, $x_0=0$, $w_k$ i.i.d. uniform on $\{\pm1\}$, $\|\cdot\|_s=|\cdot|$, $\theta=1$: (2)(a) claims $\mathbb E[x_k^2]\le c_1(1-(1-\beta)\alpha)^k\to0$, but $\mathbb E[x_k^2]\to\alpha/(2-\alpha)>0$
--   - reading: $\{Y_k\}$ is a Markov chain and $\{w_k\}$ a random process; their joint law is not stated → $Y$ is Markov with matrix $P$ relative to a filtration $\mathcal G$ to which $Y$ and the iterates are adapted; reason: the proof (p.34) conditions the chain on past iterates; with $w\equiv0$ the natural filtration of $Y$ qualifies
--   - reading: $K=\min\{k\ge0:k\ge t_k\}$, then used as if $t_k\le k$ for all $k\ge K$ → $K$ = least $K_0$ with $t_k\le k$ for every $k\ge K_0$; reason: with the printed $K$ the right side can contain a negative index (two-state chain whose stepsize drops by a factor 8 after step $m$); the proof uses the read $K$
--   - reading: initial estimate $x_0$ → a fixed vector $x_0$; the law of $Y_0$ is arbitrary; reason: $c_1$ contains $\|x_0\|_c$ and part (1) bounds $\|x_k-x^*\|_c^2$ a.s. by a constant
--   - reading: Condition 2.1 (2), (3): 'there exists a threshold $\bar h$' for $h$ (specified in App. A.2) → admissibility: Condition A.1, $t_k\ge1$, $\alpha_{k-t_k}\le2\alpha_k$, and $h\ge[2\xi/(\varphi_2\alpha)]^{1/(1-\xi)}$ for $\xi<1$; reason: Theorem A.3 prints a weaker condition on $\bar h$ than its proof (pp.29–30) establishes and uses; these are the proof's conditions
--   - generalization: the bounds for $h\ge\bar h$ and $\alpha\in(0,\bar\alpha)$ for chosen thresholds → the thresholds exist, and the bounds hold for every admissible $(\alpha,h)$ and every $\bar\alpha$ with the property of Theorem A.3 (a); reason: every $(\alpha,h)$ above the existing threshold is admissible, so this implies the source's form
--   - encoding: unique stationary distribution $\mu$ → $\mu$ stationary; uniqueness not assumed; reason: uniqueness follows from the geometric decay of Assumption 2.3
--   - encoding: $\mathbb R^d$ with an arbitrary norm $\|\cdot\|_c$ → a finite-dimensional real normed space $E$ with its norm; reason: the same spaces up to linear isometry; $d$ does not appear in the statement
--   - reading: $\|\cdot\|_s$, $\ell_{cs}$, $u_{cs}$, $\theta$ 'properly chosen' → any smoothing data meeting the conditions of p.24; reason: the paper fixes one such choice without specifying it; the claim holds for each
--   - generalization: $\|w_k\|_c\le A_2\|x_k\|_c+B_2$ (no qualifier) → the same bound almost surely; reason: a pathwise bound implies the almost-sure one, so the statement specializes to the source's
--   - encoding: $\{w_k\}$ a random process → each $w_k$ measurable; reason: needed for $\mathbb E[w_k\mid\mathcal F_k]$ to be defined; it excludes only undefined cases
--   - reading: $\ell_{cs}\|\cdot\|_c\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$ (as printed, p.24) → $\ell_{cs}\|\cdot\|_s\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$; reason: the left norm is a misprint: read literally it only says $\ell_{cs}\le1$, while pp.30 and 34 use $\|\cdot\|_s\le\|\cdot\|_c/\ell_{cs}$
--   - encoding: the norm $\|\cdot\|_s$ → a function with the norm axioms; reason: same objects
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Theorem 2.1, pp.6–7 (restated as Theorem A.3, p.28)

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_MarkovSA_Fbar
import Definitions.Def_MarkovSA_saIter
import Definitions.Def_MarkovSA_IsSAInstance
import Definitions.Def_MarkovSA_Assumption23
import Definitions.Def_MarkovSA_IsSmoothingData
import Definitions.Def_MarkovSA_phi1
import Definitions.Def_MarkovSA_phi2
import Definitions.Def_MarkovSA_phi3
import Definitions.Def_MarkovSA_Aconst
import Definitions.Def_MarkovSA_Bconst
import Definitions.Def_MarkovSA_c1
import Definitions.Def_MarkovSA_c2
import Definitions.Def_MarkovSA_stepMix
import Definitions.Def_MarkovSA_Kidx
import Definitions.Def_MarkovSA_polyStep
import Definitions.Def_MarkovSA_Admissible
open MeasureTheory

namespace MarkovSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴] [MeasurableSpace 𝒴] [MeasurableSingletonClass 𝒴]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Theorem 2.1** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §2.2, pp.6–7; restated in full as Theorem A.3, p.28), corrected: `𝒴` has at least two
points (C1). Consider the iterates `x_k` of Algorithm (6) under Assumptions 2.1–2.4, with the constants
`A = A₁ + A₂ + 1`, `B = B₁ + B₂`, `c₁ = (‖x₀ − x*‖_c + ‖x₀‖_c + B/A)²`, `c₂ = (A‖x*‖_c + B)²` and `φ₁, φ₂, φ₃` of
Eq. (16) for any admissible smoothing data. Let `T = min(φ₂/(φ₃A²), 1/(4A))`. Then:
1. (Condition 2.1) a threshold `ᾱ ∈ (0, 1)` with `αt_α ≤ T` for all `α ∈ (0, ᾱ)` exists, and for `ξ = 1` and each
`ξ ∈ (0, 1)`, every `α > 0` has a threshold `h̄` above which `(α, h)` is admissible;
2. (constant stepsize, (1) and (2)(a)) for every such `ᾱ` and `α ∈ (0, ᾱ)`: `‖x_k − x*‖_c² ≤ c₁` a.s. for `k < t_α`, and
`E‖x_k − x*‖_c² ≤ φ₁c₁(1 − φ₂α)^{k−t_α} + (φ₃c₂/φ₂)αt_α` for `k ≥ t_α`;
3. (linear stepsize `α/(k + h)`, (1) and (2)(b)) for every admissible `(α, h)`: the a.s. bound for `k < K`, and for `k ≥ K`
the bounds (i) `α < 1/φ₂`, (ii) `α = 1/φ₂`, (iii) `α > 1/φ₂`;
4. (polynomial stepsize `α/(k + h)^ξ`, `ξ ∈ (0, 1)`, (1) and (2)(c)) for every admissible `(α, h)`: the a.s. bound for
`k < K`, and the bound (c) for `k ≥ K`.

**Formalization Note.** `‖·‖_c` is the norm of the finite-dimensional real normed space `E` (R6); `‖·‖_s` and the
smoothing data are any admissible choice (R7). `x₀` is a fixed vector; the chain is Markov relative to a filtration
`G` to which the iterates are adapted (R1); Assumption 2.4 (2) holds a.s. (R8). `K` is the least `K₀` with `t_k ≤ k`
for all `k ≥ K₀` (R2); for constant stepsizes it is `t_α`. "Admissible" is reading R4. `[Nontrivial 𝒴]` is the
correction C1, deliberately not a default. `e = Real.exp 1`. -/
theorem theorem_2_1 [Nontrivial 𝒴] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (C σ : ℝ) (hchain : Assumption23 P μ C σ)
    (β A₁ B₁ A₂ B₂ : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (s : E → ℝ) (L ℓ u θ : ℝ) (hsm : IsSmoothingData s L ℓ u θ β)
    (F : E → 𝒴 → E) (x₀ xstar : E) (Y : ℕ → Ω → 𝒴) (G : Filtration ℕ mΩ) (w : ℕ → Ω → E) :
    ((∃ αbar : ℝ, 0 < αbar ∧ αbar < 1 ∧ ∀ a : ℝ, 0 < a → a < αbar →
        a * (MarkovMixing.mixingTime P μ a : ℝ) ≤ min (phi2 β ℓ u θ / (phi3 L ℓ u θ * Aconst A₁ A₂ ^ 2)) (1 / (4 * Aconst A₁ A₂))) ∧
      (∀ a : ℝ, 0 < a → ∃ hbar : ℝ, 0 < hbar ∧ ∀ h : ℝ, hbar ≤ h → Admissible P μ (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂) a 1 h) ∧
      (∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ a : ℝ, 0 < a →
        ∃ hbar : ℝ, 0 < hbar ∧ ∀ h : ℝ, hbar ≤ h → Admissible P μ (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂) a ξ h)) ∧
    (∀ αbar : ℝ, 0 < αbar → αbar < 1 →
      (∀ a : ℝ, 0 < a → a < αbar → a * (MarkovMixing.mixingTime P μ a : ℝ) ≤ min (phi2 β ℓ u θ / (phi3 L ℓ u θ * Aconst A₁ A₂ ^ 2)) (1 / (4 * Aconst A₁ A₂))) →
      ∀ a : ℝ, 0 < a → a < αbar → IsSAInstance Pr P μ β A₁ B₁ A₂ B₂ (fun _ => a) F x₀ xstar Y G w →
        (∀ k : ℕ, k < MarkovMixing.mixingTime P μ a → ∀ᵐ ω ∂Pr, ‖saIter F (fun _ => a) x₀ Y w k ω - xstar‖ ^ 2 ≤ c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂)) ∧
        ∀ k : ℕ, MarkovMixing.mixingTime P μ a ≤ k →
          ∫ ω, ‖saIter F (fun _ => a) x₀ Y w k ω - xstar‖ ^ 2 ∂Pr ≤
            phi1 ℓ u θ * c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂) * (1 - phi2 β ℓ u θ * a) ^ (k - MarkovMixing.mixingTime P μ a) +
              phi3 L ℓ u θ * c2 xstar (Aconst A₁ A₂) (Bconst B₁ B₂) / phi2 β ℓ u θ * (a * (MarkovMixing.mixingTime P μ a : ℝ))) ∧
    (∀ a h : ℝ, 0 < a → 0 < h → Admissible P μ (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂) a 1 h → IsSAInstance Pr P μ β A₁ B₁ A₂ B₂ (polyStep a h 1) F x₀ xstar Y G w →
      (∀ k : ℕ, k < Kidx (stepMix P μ (polyStep a h 1)) → ∀ᵐ ω ∂Pr, ‖saIter F (polyStep a h 1) x₀ Y w k ω - xstar‖ ^ 2 ≤ c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂)) ∧
      ∀ k : ℕ, Kidx (stepMix P μ (polyStep a h 1)) ≤ k →
        (a < 1 / phi2 β ℓ u θ →
          ∫ ω, ‖saIter F (polyStep a h 1) x₀ Y w k ω - xstar‖ ^ 2 ∂Pr ≤
            phi1 ℓ u θ * c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂) * (((Kidx (stepMix P μ (polyStep a h 1)) : ℕ) + h) / ((k : ℝ) + h)) ^ (phi2 β ℓ u θ * a) +
              8 * a ^ 2 * phi3 L ℓ u θ * c2 xstar (Aconst A₁ A₂) (Bconst B₁ B₂) / (1 - phi2 β ℓ u θ * a) * ((stepMix P μ (polyStep a h 1) k : ℝ) / ((k : ℝ) + h) ^ (phi2 β ℓ u θ * a))) ∧
        (a = 1 / phi2 β ℓ u θ →
          ∫ ω, ‖saIter F (polyStep a h 1) x₀ Y w k ω - xstar‖ ^ 2 ∂Pr ≤
            phi1 ℓ u θ * c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂) * (((Kidx (stepMix P μ (polyStep a h 1)) : ℕ) + h) / ((k : ℝ) + h)) +
              8 * a ^ 2 * phi3 L ℓ u θ * c2 xstar (Aconst A₁ A₂) (Bconst B₁ B₂) * ((stepMix P μ (polyStep a h 1) k : ℝ) * Real.log ((k : ℝ) + h) / ((k : ℝ) + h))) ∧
        (1 / phi2 β ℓ u θ < a →
          ∫ ω, ‖saIter F (polyStep a h 1) x₀ Y w k ω - xstar‖ ^ 2 ∂Pr ≤
            phi1 ℓ u θ * c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂) * (((Kidx (stepMix P μ (polyStep a h 1)) : ℕ) + h) / ((k : ℝ) + h)) ^ (phi2 β ℓ u θ * a) +
              8 * Real.exp 1 * a ^ 2 * phi3 L ℓ u θ * c2 xstar (Aconst A₁ A₂) (Bconst B₁ B₂) / (phi2 β ℓ u θ * a - 1) * ((stepMix P μ (polyStep a h 1) k : ℝ) / ((k : ℝ) + h)))) ∧
    (∀ ξ a h : ℝ, 0 < ξ → ξ < 1 → 0 < a → 0 < h → Admissible P μ (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂) a ξ h → IsSAInstance Pr P μ β A₁ B₁ A₂ B₂ (polyStep a h ξ) F x₀ xstar Y G w →
      (∀ k : ℕ, k < Kidx (stepMix P μ (polyStep a h ξ)) → ∀ᵐ ω ∂Pr, ‖saIter F (polyStep a h ξ) x₀ Y w k ω - xstar‖ ^ 2 ≤ c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂)) ∧
      ∀ k : ℕ, Kidx (stepMix P μ (polyStep a h ξ)) ≤ k →
        ∫ ω, ‖saIter F (polyStep a h ξ) x₀ Y w k ω - xstar‖ ^ 2 ∂Pr ≤
          phi1 ℓ u θ * c1 x₀ xstar (Aconst A₁ A₂) (Bconst B₁ B₂) * Real.exp (-(phi2 β ℓ u θ * a / (1 - ξ)) * (((k : ℝ) + h) ^ (1 - ξ) - ((Kidx (stepMix P μ (polyStep a h ξ)) : ℕ) + h) ^ (1 - ξ))) +
            4 * phi3 L ℓ u θ * c2 xstar (Aconst A₁ A₂) (Bconst B₁ B₂) * a / phi2 β ℓ u θ * ((stepMix P μ (polyStep a h ξ) k : ℝ) / ((k : ℝ) + h) ^ ξ)) := by sorry

end MarkovSA
