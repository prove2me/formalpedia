-- Prove2me | Theorems.Thm_OnlineUBSR_theorem_1
-- name    : OnlineUBSR.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:20:32.540188+00:00
-- url     : https://prove2.me/theorems/e0f96d4c-1069-4d1b-8d4b-142417149e45
-- title:
--   Theorem 1 — $\mathbb E[(t_n-SR_\lambda(X))^2]=O(1/n)$ with an explicit constant (corrected: Assumption 3 on $g'$, Assumption 4 from $n=0$, $t_0\in[t_l,t_u]$)
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $X$ a random variable with $|X|\le M_0$ a.s. (Assumption 2). Let $\ell:\mathbb R\to\mathbb R$ be convex and differentiable, $\lambda\in\mathbb R$, $g(t)=\mathbb E[\ell(-X-t)]-\lambda$, and $SR_\lambda(X)=\inf\{t:\ t+X\in\mathcal A\}$ the utility-based shortfall risk. Assume:
--
--   1. (Assumption 1) $t_l<t_u$, $g(t_l)>0$ and $g(t_u)<0$;
--   2. (Assumption 3, corrected) $\mu_1,L_1>0$ and $-L_1\le g'(t)\le-\mu_1$ for all $t\in[t_l,t_u]$;
--   3. $\xi_1,\xi_2,\dots$ are independent random variables, each distributed as $-X$;
--   4. $t_0\in[t_l,t_u]$ is deterministic, $c$ satisfies $\tfrac12<\mu_1c$, and $t_n=\Gamma\big(t_{n-1}+\tfrac cn(\ell(\xi_n-t_{n-1})-\lambda)\big)$ with $\Gamma(x)=\min(\max(t_l,x),t_u)$;
--   5. (Assumption 4, corrected) with $\varepsilon_n=\ell(\xi_{n+1}-t_n)-\lambda-g(t_n)$ and $\mathcal F_n=\sigma(t_0,\dots,t_n)$, there is $\sigma>0$ with $\mathbb E[\varepsilon_n^2\mid\mathcal F_n]\le\sigma^2$ a.s. for all $n\ge0$.
--
--   Then for every $n\ge1$
--
--   $$
--   \mathbb E\big[(t_n-SR_\lambda(X))^2\big]\le\exp\Big(\frac{L_1^2c^2\pi^2}{6}\Big)\left[\frac{(t_0-SR_\lambda(X))^2}{n^{2\mu_1c}}+\frac{\sigma^2\,2^{2\mu_1c}\,c^2}{(2\mu_1c-1)\,n}\right].
--   $$
--
--   The projected stochastic approximation estimator therefore has mean-squared error $O(1/n)$, with an explicit constant, using one sample of $-X$ per step; the initial error is forgotten at rate $n^{-2\mu_1c}$, faster than $1/n$.
--
--   **Formalization Note** The iterates are `OnlineUBSR.iterate` with `a k = c / k`, $\varepsilon_n$ is `OnlineUBSR.noise`, $\mathcal F_n$ is `OnlineUBSR.iterSigma`, and $SR_\lambda(X)$ is the real infimum `OnlineUBSR.ubsr` (finite here by `OnlineUBSR.sr_is_root`). Expectations are Bochner integrals and conditional expectations are `condExp`; all integrands are bounded a.s. The powers $n^{2\mu_1c}$ and $2^{2\mu_1c}$ are real powers. $c>0$ follows from $\mu_1>0$ and $\mu_1c>\tfrac12$.
--
--   Differences from the source:
--   - correction: Assumption 3 (p.5): −L₁ ≤ −ℓ′(−t) ≤ −µ₁ for all t ∈ [t_l, t_u] → −L₁ ≤ g′(t) ≤ −µ₁ for all t ∈ [t_l, t_u], with g′ the derivative of g; reason: the printed form is false: X ≡ 10, t_l = 0, t_u = 2, a C¹ convex ℓ with ℓ′ = 0.1 on (−∞, −10] and ℓ′ = 1 on [−2, ∞), λ = ℓ(−11), c = 1, t₀ = 0 meet every printed assumption with µ₁ = L₁ = 1, yet E[z₁₀₀²] = 0.348 > 0.208, the right side of (6); the proof (p.18) uses bounds on g′(t) = −E[ℓ′(−X − t)], which is −ℓ′(−t) only when X ≡ 0
--   - correction: Assumption 4 (p.5): E[ε_n² | 𝓕_n] ≤ σ² a.s. for all n ≥ 1 → for all n ≥ 0; reason: the proof applies the bound to E[ε₀² | 𝓕₀] in (28) at n = 1; with the bound only for n ≥ 1, P(ξ = 1) = 10⁻⁴, P(ξ = 0) = 1 − 10⁻⁴, X = −ξ, a steep convex ℓ above 1, λ = −10⁻⁴, t_l = t₀ = −0.01, t_u = 110, c = 1 give E[z₁²] = 1.02 > 0.363, the right side of (6) at n = 1
--   - correction: t₀ unrestricted → t₀ ∈ [t_l, t_u]; reason: (28)–(30) use J₀ = J(t₀), and (27) holds only inside [t_l, t_u]; X ≡ 0, t_l = 0, t_u = 10, g(t) = 1 − t on [0, 10], ℓ(1) ≥ λ + 11, σ = 0.01, c = 1 and t₀ = −1 give t₁ = 10 and E[z₁²] = 81 > 20.7, the right side of (6) at n = 1
--   - reading: ε_n = ĝ(t_n) − g(t_n), with ĝ(t) = ℓ(ξ_n − t) − λ and the sample in ε_n unnamed → ε_n = ℓ(ξ_{n+1} − t_n) − λ − g(t_n), the fresh sample; reason: (26) writes t_n = Γ(t_{n−1} + a_n(g(t_{n−1}) + ε_{n−1})), so ε_{n−1} uses ξ_n; only this reading makes ε_n centred given 𝓕_n
--   - generalization: ℓ convex and monotone (§3, p.4) → ℓ convex (and differentiable, p.5); monotonicity not assumed; reason: only the root of g inside [t_l, t_u] is used, and convexity with Assumption 1 gives it; with a monotone ℓ the hypotheses are the page's
--   - encoding: λ in the interior of the range of ℓ (§2, p.3) → not assumed; reason: implied by Assumption 1 (g(t_l) > 0 > g(t_u)) and the continuity of the convex ℓ, so no instance changes
--   - encoding: the interval [t_l, t_u] of Assumption 3 and of Γ → t_l < t_u; reason: the page treats [t_l, t_u] as a nondegenerate interval; for a monotone ℓ, g(t_l) > 0 > g(t_u) forces it
--   - encoding: SR_λ(X) = inf{t ∈ ℝ : t + X ∈ A} (2) → the real sInf (OnlineUBSR.ubsr); reason: under the hypotheses the set is nonempty and bounded below (OnlineUBSR.sr_is_root), so the infimum is finite and no junk value occurs
--   - encoding: random variables; an i.i.d. sequence {ξ_i} from the distribution of −X; expectations → measurable functions on a probability space; ξ 1, ξ 2, … mutually independent (iIndepFun) and each identically distributed with −X; Bochner integrals and condExp; ξ 0 and a 0 unread; reason: same instances; every integrand is bounded a.s. and 𝓕_n is a sub-σ-algebra (verification files)
--   - encoding: step size a_k = c/k → a k = c / k for k ≥ 1, a 0 unread; reason: the recursion never reads a 0
--   - encoding: "for all n" (Remark 2) → n ≥ 1; reason: (6) divides by n; at n = 0 the right side is undefined on the page
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, Theorem 1, eq. (6), p.5; proof §7.1, pp.18–19

import Mathlib
import Definitions.Def_OnlineUBSR_gFun
import Definitions.Def_OnlineUBSR_acceptanceSet
import Definitions.Def_OnlineUBSR_ubsr
import Definitions.Def_OnlineUBSR_proj
import Definitions.Def_OnlineUBSR_iterate
import Definitions.Def_OnlineUBSR_noise
import Definitions.Def_OnlineUBSR_iterSigma

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR

/-- **Theorem 1 (mean-squared error of the projected SA estimator of shortfall risk).**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, Theorem 1, p.5: "Suppose Assumptions 1 to 4 hold. Setting the step size ak = c/k with
1/2 < µ1c, we have E[(tn − SRλ(X))²] ≤ exp(L1²c²π²/6) [ (t0 − SRλ(X))²/n^{2µ1c} +
σ²2^{2µ1c}c²/((2µ1c − 1)n) ]. (6)" Proof: §7.1, pp.18–19.

Let `t_n` be the recursion (5) (`OnlineUBSR.iterate`) with step sizes `a_k = c/k`. Then for every
`n ≥ 1`,
`E[(t_n − SR_λ(X))²] ≤ exp(L₁²c²π²/6) ((t₀ − SR_λ(X))²/n^{2μ₁c} + σ²2^{2μ₁c}c²/((2μ₁c − 1)n))`.

**Formalization Note.** Hypotheses: `(Ω, μ)` a probability space; `X` measurable with
`|X| ≤ M₀` a.s. (Assumption 2); the samples `ξ 1, ξ 2, …` measurable, independent and each
distributed as `−X`; `ℓ` convex and differentiable on `ℝ`; `t_l < t_u` with
`g(t_l) > 0 > g(t_u)` (Assumption 1); `μ₁, L₁ > 0` with `−L₁ ≤ g′(t) ≤ −μ₁` on `[t_l, t_u]`
(Assumption 3, corrected: the page bounds `−ℓ′(−t)`, which equals `g′(t)` only when `X ≡ 0`;
the proof uses `g′`); `σ > 0` with `E[ε_n² | 𝓕_n] ≤ σ²` a.s. for every `n ≥ 0` (Assumption 4,
corrected from `n ≥ 1`: the proof uses `n = 0`); `t₀ ∈ [t_l, t_u]` (corrected: the page leaves
`t₀` free). `ε_n` uses the fresh sample `ξ_{n+1}` (`OnlineUBSR.noise`); `𝓕_n` is the σ-field
generated by `t_0, …, t_n` (`OnlineUBSR.iterSigma`). `SR_λ(X)` is the real infimum (2)
(`OnlineUBSR.ubsr`), finite here by `OnlineUBSR.sr_is_root`. `t₀` is deterministic, samples are
indexed from `1` (`ξ 0`, `a 0` unread), the powers `n^{2μ₁c}` and `2^{2μ₁c}` are real powers, and
`n ≥ 1` because the bound divides by `n`. Monotonicity of `ℓ` and "λ in the interior of the
range of ℓ" are not assumed. `c > 0` follows from `μ₁ > 0` and `μ₁c > 1/2`. -/
theorem theorem_1
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : Measurable X)
    (ξ : ℕ → Ω → ℝ) (hξ : ∀ n, Measurable (ξ (n + 1)))
    (hind : iIndepFun (fun n => ξ (n + 1)) μ)
    (hident : ∀ n, IdentDistrib (ξ (n + 1)) (fun ω => -X ω) μ μ)
    (ℓ : ℝ → ℝ) (hℓconv : ConvexOn ℝ Set.univ ℓ) (hℓdiff : Differentiable ℝ ℓ)
    (lam tl tu : ℝ) (htlu : tl < tu)
    (hA1l : 0 < gFun μ ℓ lam X tl) (hA1u : gFun μ ℓ lam X tu < 0)
    (M₀ : ℝ) (hA2 : ∀ᵐ ω ∂μ, |X ω| ≤ M₀)
    (μ₁ L₁ : ℝ) (hμ₁ : 0 < μ₁) (hL₁ : 0 < L₁)
    (hA3 : ∀ t ∈ Set.Icc tl tu,
      -L₁ ≤ deriv (gFun μ ℓ lam X) t ∧ deriv (gFun μ ℓ lam X) t ≤ -μ₁)
    (σ : ℝ) (hσ : 0 < σ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Icc tl tu)
    (c : ℝ) (hc : 1 / 2 < μ₁ * c)
    (hA4 : ∀ n : ℕ, μ[fun ω => noise μ ℓ lam X (iterate ℓ lam tl tu t₀ (fun k : ℕ => c / (k : ℝ)) ξ) ξ n ω ^ 2 |
        iterSigma (iterate ℓ lam tl tu t₀ (fun k : ℕ => c / (k : ℝ)) ξ) n] ≤ᵐ[μ] fun _ => σ ^ 2)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫ ω, (iterate ℓ lam tl tu t₀ (fun k : ℕ => c / (k : ℝ)) ξ n ω - ubsr μ ℓ lam X) ^ 2 ∂μ ≤
      Real.exp (L₁ ^ 2 * c ^ 2 * π ^ 2 / 6) *
        ((t₀ - ubsr μ ℓ lam X) ^ 2 / (n : ℝ) ^ (2 * μ₁ * c) +
          σ ^ 2 * (2 : ℝ) ^ (2 * μ₁ * c) * c ^ 2 / ((2 * μ₁ * c - 1) * n)) := by sorry

end OnlineUBSR
