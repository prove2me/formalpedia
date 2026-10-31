-- Prove2me | Theorems.Thm_OnlineUBSR_eq_27
-- name    : OnlineUBSR.eq_27
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:21:06.683278+00:00
-- url     : https://prove2.me/theorems/bd6d6a6c-3bd1-4d29-bbbb-70c318120bbe
-- title:
--   (27), p.18 — $-L_1\le J(t)\le-\mu_1$ and $g(t)=J(t)(t-SR_\lambda(X))$ (corrected: Assumptions 3, 4, $t_0\in[t_l,t_u]$)
-- statement:
--   Throughout, $(\Omega,\mathcal F,\mathbb P)$ is a probability space; $X$ is a random variable with $|X|\le M_0$ a.s. (Assumption 2); $\xi_1,\xi_2,\dots$ are independent random variables, each distributed as $-X$; $\ell:\mathbb R\to\mathbb R$ is convex and differentiable; $t_l<t_u$ with $g(t_l)>0>g(t_u)$, where $g(t)=\mathbb E[\ell(-X-t)]-\lambda$ (Assumption 1); $\mu_1,L_1>0$ with $-L_1\le g'(t)\le-\mu_1$ for $t\in[t_l,t_u]$ (Assumption 3, corrected); $t_0\in[t_l,t_u]$; $a_k>0$ for $k\ge1$; the iterates are $t_{n+1}=\Gamma\big(t_n+a_{n+1}(\ell(\xi_{n+1}-t_n)-\lambda)\big)$ with $\Gamma(x)=\min(\max(t_l,x),t_u)$; $\varepsilon_n=\ell(\xi_{n+1}-t_n)-\lambda-g(t_n)$; $\mathcal F_n=\sigma(t_0,\dots,t_n)$; and $\sigma>0$ with $\mathbb E[\varepsilon_n^2\mid\mathcal F_n]\le\sigma^2$ a.s. for all $n\ge0$ (Assumption 4, corrected). Write $z_n=t_n-SR_\lambda(X)$.
--
--   Let $J(t)=\int_0^1 g'\big(mt+(1-m)SR_\lambda(X)\big)\,dm$. Then for every $t\in[t_l,t_u]$
--
--   $$
--   -L_1\le J(t)\le-\mu_1\qquad\text{and}\qquad g(t)=J(t)\,\big(t-SR_\lambda(X)\big),
--   $$
--
--   and $J$ is continuous on $[t_l,t_u]$. Applied at $t=t_k$ this gives $J_k\le-\mu_1$ and $g(t_k)=J_kz_k$.
--
--   **Formalization Note** The step sequence is a general `a : ℕ → ℝ` (`a 0` unread); the iterates are `OnlineUBSR.iterate`, $\varepsilon_n$ is `OnlineUBSR.noise`, $\mathcal F_n$ is `OnlineUBSR.iterSigma`, $g$ is `OnlineUBSR.gFun` and $SR_\lambda(X)$ is the real infimum `OnlineUBSR.ubsr`. Expectations are Bochner integrals and conditional expectations are Mathlib's `condExp`; all integrands are bounded a.s.
--
--   Differences from the source:
--   - correction: Assumption 3 (p.5): −L₁ ≤ −ℓ′(−t) ≤ −µ₁ for all t ∈ [t_l, t_u] → −L₁ ≤ g′(t) ≤ −µ₁ for all t ∈ [t_l, t_u], with g′ the derivative of g; reason: the printed form is false: X ≡ 10, t_l = 0, t_u = 2, a C¹ convex ℓ with ℓ′ = 0.1 on (−∞, −10] and ℓ′ = 1 on [−2, ∞), λ = ℓ(−11), c = 1, t₀ = 0 meet every printed assumption with µ₁ = L₁ = 1, yet E[z₁₀₀²] = 0.348 > 0.208, the right side of (6); the proof (p.18) uses bounds on g′(t) = −E[ℓ′(−X − t)], which is −ℓ′(−t) only when X ≡ 0
--   - correction: Assumption 4 (p.5): E[ε_n² | 𝓕_n] ≤ σ² a.s. for all n ≥ 1 → for all n ≥ 0; reason: the proof applies the bound to E[ε₀² | 𝓕₀] in (28) at n = 1; with the bound only for n ≥ 1, P(ξ = 1) = 10⁻⁴, P(ξ = 0) = 1 − 10⁻⁴, X = −ξ, a steep convex ℓ above 1, λ = −10⁻⁴, t_l = t₀ = −0.01, t_u = 110, c = 1 give E[z₁²] = 1.02 > 0.363, the right side of (6) at n = 1
--   - correction: t₀ unrestricted → t₀ ∈ [t_l, t_u]; reason: (28)–(30) use J₀ = J(t₀), and (27) holds only inside [t_l, t_u]; X ≡ 0, t_l = 0, t_u = 10, g(t) = 1 − t on [0, 10], ℓ(1) ≥ λ + 11, σ = 0.01, c = 1 and t₀ = −1 give t₁ = 10 and E[z₁²] = 81 > 20.7, the right side of (6) at n = 1
--   - reading: ε_n = ĝ(t_n) − g(t_n), with ĝ(t) = ℓ(ξ_n − t) − λ and the sample in ε_n unnamed → ε_n = ℓ(ξ_{n+1} − t_n) − λ − g(t_n), the fresh sample; reason: (26) writes t_n = Γ(t_{n−1} + a_n(g(t_{n−1}) + ε_{n−1})), so ε_{n−1} uses ξ_n; only this reading makes ε_n centred given 𝓕_n
--   - generalization: ℓ convex and monotone (§3, p.4) → ℓ convex (and differentiable, p.5); monotonicity not assumed; reason: only the root of g inside [t_l, t_u] is used, and convexity with Assumption 1 gives it; with a monotone ℓ the hypotheses are the page's
--   - encoding: λ in the interior of the range of ℓ (§2, p.3) → not assumed; reason: implied by Assumption 1 (g(t_l) > 0 > g(t_u)) and the continuity of the convex ℓ, so no instance changes
--   - generalization: step sizes a_k = c/k with 1/2 < µ₁c (Theorem 1) → any step sequence a with a_k > 0 for k ≥ 1; reason: the proof up to (30) uses a general a_n ("The passage leading up to (30) holds for any choice of stepsize", p.21); a_k = c/k is a special case
--   - encoding: the interval [t_l, t_u] of Assumption 3 and of Γ → t_l < t_u; reason: the page treats [t_l, t_u] as a nondegenerate interval; for a monotone ℓ, g(t_l) > 0 > g(t_u) forces it
--   - encoding: SR_λ(X) = inf{t ∈ ℝ : t + X ∈ A} (2) → the real sInf (OnlineUBSR.ubsr); reason: under the hypotheses the set is nonempty and bounded below (OnlineUBSR.sr_is_root), so the infimum is finite and no junk value occurs
--   - encoding: random variables; an i.i.d. sequence {ξ_i} from the distribution of −X; expectations → measurable functions on a probability space; ξ 1, ξ 2, … mutually independent (iIndepFun) and each identically distributed with −X; Bochner integrals and condExp; ξ 0 and a 0 unread; reason: same instances; every integrand is bounded a.s. and 𝓕_n is a sub-σ-algebra (verification files)
--   - generalization: J_k ≤ −µ₁ and g(t_n) = J_n z_n for k, n ≥ 1 → for every t ∈ [t_l, t_u] (so for every t_k, including t₀), plus −L₁ ≤ J(t) and continuity of J on [t_l, t_u]; reason: the proof uses J₀ in (28)–(30) and −L₁ ≤ J_k in (29); continuity makes J(t_k) 𝓕_k-measurable
-- source:
--   Hegde, Menon, Prashanth & Jagannathan, Online Estimation and Optimization of Utility-Based Shortfall Risk, arXiv:2111.08805v3, §7.1, eq. (27) and the display after it, p.18

import Mathlib
import Definitions.Def_OnlineUBSR_gFun
import Definitions.Def_OnlineUBSR_acceptanceSet
import Definitions.Def_OnlineUBSR_ubsr
import Definitions.Def_OnlineUBSR_proj
import Definitions.Def_OnlineUBSR_iterate
import Definitions.Def_OnlineUBSR_noise
import Definitions.Def_OnlineUBSR_iterSigma
import Definitions.Def_OnlineUBSR_Jfun

open MeasureTheory ProbabilityTheory Real

namespace OnlineUBSR

/-- **The averaged derivative `J` of (27): bounds and the identity `g(t) = J(t)(t − SR_λ(X))`.**
Hegde, Menon, Prashanth & Jagannathan, arXiv:2111.08805v3, §7.1, (27), p.18: "For any k ≥ 1, define Jk = ∫₀¹ g′(mtk + (1 − m)SRλ(X))dm. (27) Using
Assumption 3, we obtain Jk ≤ −µ1, for all k ≥ 1. Using Jn we can express g(tn) as,
g(tn) = ∫₀¹ g′(mtn + (1 − m)SRλ(X))dm(tn − SRλ(X)) = Jnzn."

For every `t ∈ [t_l, t_u]`, with `J(t) = ∫_0^1 g′(m t + (1 − m) SR_λ(X)) dm`
(`OnlineUBSR.Jfun`): `−L₁ ≤ J(t) ≤ −μ₁` and `g(t) = J(t)(t − SR_λ(X))`. Moreover `J` is
continuous on `[t_l, t_u]`, so `J(t_k)` is a measurable function of `t_k`.

The page states the bound for `J_k = J(t_k)`, `k ≥ 1`; the proof also uses `J_0` in (28)–(30),
so it is stated here at every point of `[t_l, t_u]`, which covers every `t_k` (including `t_0`).
The lower bound `−L₁ ≤ J_k` is the one used in (29) ("−L1 ≤ Jk ≤ −µ1").

**Formalization Note.** The standing hypotheses are those of Theorem 1 (pp.4–5), for a general
positive step sequence `a` (`a 0` is never read): `(Ω, μ)` a probability space; `X` measurable with
`|X| ≤ M₀` a.s. (Assumption 2); the samples `ξ 1, ξ 2, …` measurable, independent and each
distributed as `−X`; `ℓ` convex and differentiable on `ℝ`; `t_l < t_u` with `g(t_l) > 0 > g(t_u)`
(Assumption 1); `μ₁, L₁ > 0` with `−L₁ ≤ g′(t) ≤ −μ₁` on `[t_l, t_u]` (Assumption 3, corrected:
the page bounds `−ℓ′(−t)`, which is `g′(t)` only when `X ≡ 0`); `σ > 0` with
`E[ε_n² | 𝓕_n] ≤ σ²` a.s. for every `n ≥ 0` (Assumption 4, corrected: the page says `n ≥ 1`,
the proof uses `n = 0`); `t₀ ∈ [t_l, t_u]` (corrected: the page leaves `t₀` free, but (27) is
applied at `k = 0`). `ε_n` uses the fresh sample `ξ_{n+1}` (`OnlineUBSR.noise`), and `𝓕_n` is
the σ-field of `t_0, …, t_n` (`OnlineUBSR.iterSigma`). -/
theorem eq_27
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
    (a : ℕ → ℝ) (ha : ∀ k, 1 ≤ k → 0 < a k)
    (hA4 : ∀ n : ℕ, μ[fun ω => noise μ ℓ lam X (iterate ℓ lam tl tu t₀ a ξ) ξ n ω ^ 2 |
        iterSigma (iterate ℓ lam tl tu t₀ a ξ) n] ≤ᵐ[μ] fun _ => σ ^ 2) :
    (∀ t ∈ Set.Icc tl tu,
      -L₁ ≤ Jfun μ ℓ lam X t ∧ Jfun μ ℓ lam X t ≤ -μ₁ ∧
      gFun μ ℓ lam X t = Jfun μ ℓ lam X t * (t - ubsr μ ℓ lam X)) ∧
    ContinuousOn (Jfun μ ℓ lam X) (Set.Icc tl tu) := by sorry

end OnlineUBSR
