-- Prove2me | Theorems.Thm_HalfinWhitt81_Stationary_Supplement_theorem_4
-- name    : HalfinWhitt81.Stationary.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:51:33.196695+00:00
-- url     : https://prove2.me/theorems/bc0c1139-9a95-4314-8575-6007140e42fc
-- title:
--   Theorem 4 (corrected: scale of the limit law) — stationary GI/M/n limit: Y_n(∞) ⇒ s·X(β/s) and P(Q_n(∞) ≥ n) → α(β/s)
-- statement:
--   Keep the setting and all hypotheses of Theorem 3: $\mu>0$, $\beta>0$, $GI/M/n$ queues $Q_n$ with interarrival times distributed as $u_n$, $0<\lambda_n<n\mu$, (2.2) and (3.1)(i)–(iii) with constant $c^2$. Assume moreover that $u_n$ is nonlattice for every $n\ge1$. Put
--
--   $$v=\frac{1+c^2}{2},\qquad s=\sqrt v,\qquad b=\frac{\beta}{s},\qquad \alpha(b)=\frac{\varphi(b)}{\varphi(b)+b\,\Phi(b)} .$$
--
--   Then:
--
--   1. for each $n\ge1$ the law of $Q_n(t)$ converges as $t\to\infty$ to a probability law on $\{0,1,2,\dots\}$, the law of $Q_n(\infty)$;
--   2. $Y_n(\infty)=(Q_n(\infty)-n)/\sqrt n\Rightarrow Y^*(\infty)$, where $Y^*(\infty)$ is distributed as $sX(b)$, with $X(b)$ the law of Theorem 1 at parameter $b$; explicitly
--   $$P(Y^*(\infty)\ge0)=\alpha(b),\quad P(Y^*(\infty)>x\mid Y^*(\infty)\ge0)=e^{-\beta x/v}\ (x\ge0),\quad P(Y^*(\infty)\le x\mid Y^*(\infty)\le0)=\frac{\Phi((\beta+x)/s)}{\Phi(\beta/s)}\ (x\le0);$$
--   3. $\lim_{n\to\infty}P(Q_n(\infty)\ge n)=P(Y^*(\infty)\ge0)=\alpha(b)$.
--
--   The paper prints the limit as "$X$ in Theorem 1 with $\beta'=2\beta/(1+c^2)$ instead of $\beta$", and $\alpha$ "with $\beta'$ instead of $\beta$". That is right only when $c^2=1$. The rate $\beta'=\beta/v$ is the correct exponential rate of the upper tail, but the mass at $[0,\infty)$ and the Gaussian lower part need $b=\beta/s$ and the spatial scale $s$ (see Differences below).
--
--   This is the result that makes the Halfin–Whitt approximation usable for non-Poisson arrivals: the ordinary time-stationary probability that all servers are busy is approximately $\alpha(\beta/s)$, and the heavy-traffic parameter is effectively rescaled by the arrival variability.
--
--   **Formalization Note** $Q_n(\infty)$ is the ordinary time-stationary number in system, obtained as the $t\to\infty$ limit (the paper's own reason for the nonlattice assumption, p. 580); its law $p_n$ is produced by the theorem, not assumed. Weak convergence of $Y_n(\infty)$ is convergence of $\sum_k p_n(k)\,g((k-n)/\sqrt n)$ for every bounded continuous $g$. "Nonlattice" means not almost surely supported on any $a+d\mathbb Z$, with $a\in\mathbb R$ and $d>0$.
--
--   Differences from the source:
--
--   - correction: Y*(∞) is distributed as X in Theorem 1 with β′ = 2β/(1+c²) instead of β, and α is (2.3) at β′ → Y*(∞) is distributed as s·X(β/s), s = √((1+c²)/2): P(Y*(∞) ≥ 0) = α(β/s), upper conditional tail e^{−βx/v}, lower conditional CDF Φ((β+x)/s)/Φ(β/s), and P(Q_n(∞) ≥ n) → α(β/s); reason: the proof (p. 581) identifies Y*(∞) as the unique stationary law of the Theorem 3 diffusion (drift −μ(β + min(x,0)), variance μ(1+c²)); Y*/s has drift −μ(β/s + min(x,0)) and variance 2μ, i.e. the Theorem 2 diffusion at β/s, whose stationary law is X(β/s) by Corollary 2; the printed law X(β′) has upper rate β/v (correct) but lower Gaussian Φ(β′+x)/Φ(β′) and mass α(β′), which differ unless c² = 1 (e.g. c² = 0, v = 1/2, printed α(2β) vs correct α(√2 β)); no case of the source domain is excluded
--   - reading: Y_n(∞) → the t → ∞ limit law of Q_n(t), whose existence (as a probability law on ℕ) is part of the conclusion; reason: p. 580 introduces the nonlattice assumption "in order that Y_n(t) ⇒ Y_n(∞) as t → ∞ for each n"
--   - reading: the standing assumption "u_n is nonlattice for each n" (p. 580) → for every n ≥ 1, a ∈ ℝ and d > 0, u_n is not a.s. in a+dℤ; reason: the nonlattice convention explicitly required by the brief, with arbitrary offset as well as positive span
--   - encoding: Y_n(∞) ⇒ Y*(∞) → ∑_k p_n(k) g((k−n)/√n) → ∫ g dν for every bounded continuous g; reason: definition of weak convergence
--   - encoding: the GI/M/n queues, (3.1)(iii), and the setup → as in Theorem 3 (one probability space, E|u_n|³ < ∞ with a uniform bound, λ_n → ∞ not stated); reason: as in Theorem 3
--   - encoding: an arrival occurs at time zero; initial state in the GI model → q0 is the independent prearrival state and Q(0)=q0+1+A(0) counts the initial batch; reason: zero interarrivals are allowed; this fixes the boundary equation without restricting their law; no initial convergence assumption is needed for the stationary result
-- source:
--   Halfin and Whitt, Heavy-Traffic Limits for Queues with Many Exponential Servers, Operations Research 29 (1981), p. 581, Theorem 4 (nonlattice assumption p. 580; scale of the limit corrected from the proof on p. 581, Theorem 3 p. 580 and Corollary 2 p. 578)

import Mathlib
import Definitions.Def_QueueingFundamentals_BirthDeath_Erlang
import Definitions.Def_HalfinWhitt81_Stationary_Basic
import Definitions.Def_HalfinWhitt81_Stationary_Supplement_Model

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace HalfinWhitt81.Stationary.Supplement

open QueueingFundamentals.BirthDeath

/-- Halfin–Whitt (1981), Theorem 4, p. 581, with the scale of its limit law corrected. Under the
hypotheses of Theorem 3 and the nonlattice condition on every `u_n`, for each `n ≥ 1` the law of
`Q_n(t)` converges as `t → ∞` to a probability law `p_n` on `ℕ` (the law of `Q_n(∞)`), and with
`v = (1 + c²)/2`, `s = √v`, `b = β/s`:
1. `Y_n(∞) = (Q_n(∞) − n)/√n ⇒ Y*(∞)`, where `P(Y*(∞) ≥ 0) = α(b)`,
   `P(Y*(∞) > x | Y*(∞) ≥ 0) = e^{−βx/v}` for `x ≥ 0` and
   `P(Y*(∞) ≤ x | Y*(∞) ≤ 0) = Φ((β + x)/s)/Φ(β/s)` for `x ≤ 0`;
2. `P(Q_n(∞) ≥ n) → α(b)`. -/
theorem theorem_4 (μ β c2 : ℝ) (hμ : 0 < μ) (hβ : 0 < β) (lam : ℕ → ℝ)
    (hlam : ∀ n : ℕ, 1 ≤ n → 0 < lam n ∧ lam n < n * μ)
    (hβlim : Tendsto (fun n : ℕ => (1 - lam n / (n * μ)) * Real.sqrt n) atTop (𝓝 β))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u : ℕ → ℕ → Ω → ℝ) (S : ℕ → Ω → ℝ → ℝ) (q0 : ℕ → Ω → ℕ) (Q : ℕ → Ω → ℝ → ℕ)
    (hsys : ∀ n : ℕ, 1 ≤ n → IsGIMnSystem P n μ (u n) (S n) (q0 n) (Q n))
    (hL3 : ∀ n : ℕ, 1 ≤ n → MemLp (u n 1) 3 P)
    (hmean : ∀ n : ℕ, 1 ≤ n → ∫ ω, u n 1 ω ∂P = 1 / lam n)
    (hvar : Tendsto (fun n : ℕ => lam n ^ 2 * variance (u n 1) P) atTop (𝓝 c2))
    (hthird : ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n → lam n ^ 3 * ∫ ω, u n 1 ω ^ 3 ∂P ≤ K)
    (hnl : ∀ n : ℕ, 1 ≤ n → IsNonlattice P (u n 1)) :
    ∃ p : ℕ → ℕ → ℝ,
      (∀ n : ℕ, 1 ≤ n → HasSum (p n) 1) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ k : ℕ,
        Tendsto (fun t : ℝ => P.real {ω | Q n ω t = k}) atTop (𝓝 (p n k))) ∧
      ∃ ν : ProbabilityMeasure ℝ,
        (ν : Measure ℝ).real (Set.Ici 0) = halfinWhittAlpha (β / diffScale c2) ∧
        (∀ x : ℝ, 0 ≤ x →
          (ν : Measure ℝ).real (Set.Ioi x) / (ν : Measure ℝ).real (Set.Ici 0) =
            Real.exp (-(β * x / ((1 + c2) / 2)))) ∧
        (∀ x : ℝ, x ≤ 0 →
          (ν : Measure ℝ).real (Set.Iic x) / (ν : Measure ℝ).real (Set.Iic 0) =
            cdf (gaussianReal 0 1) ((β + x) / diffScale c2) /
              cdf (gaussianReal 0 1) (β / diffScale c2)) ∧
        (∀ g : ℝ →ᵇ ℝ,
          Tendsto (fun n : ℕ => HalfinWhitt81.Stationary.scaledExpect (p n) n g) atTop
            (𝓝 (∫ x, g x ∂(ν : Measure ℝ)))) ∧
        Tendsto (fun n : ℕ => HalfinWhitt81.Stationary.probGE (p n) n) atTop
          (𝓝 (halfinWhittAlpha (β / diffScale c2))) := by sorry

end HalfinWhitt81.Stationary.Supplement
