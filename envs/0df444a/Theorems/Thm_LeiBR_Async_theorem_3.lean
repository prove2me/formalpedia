-- Prove2me | Theorems.Thm_LeiBR_Async_theorem_3
-- name    : LeiBR.Async.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:39.345113+00:00
-- url     : https://prove2.me/theorems/27827330-0136-4362-a84a-6f96bb9730a2
-- title:
--   Theorem 3 — the asynchronous inexact BR scheme reaches an $\epsilon$-NE$_\infty$ in at most $\ell^{(1)}_i(\eta)$ projected gradient steps per player
-- statement:
--   Consider the stochastic Nash game under Assumption 1 (with constants $M_i$) and Assumption 5, with $\mu > 0$, proximal best-response map $\hat x$ and Nash equilibrium $x^*$. Let Algorithm 3 run on a deterministic schedule $(I_k)$ with deterministic delays $\tau_{ij}(k) \le k$, $\tau_{ii}(k) = 0$, satisfying Assumption 4 with constants $B_1, B_2$. The initial profile $x_0 \in X$ is $\mathcal F_0$-measurable with
--   $$\mathbb E\big[\|x_{i,0} - x^*_i\|^2\big] \le C^2,\qquad C \ge 0 .$$
--   At time $k$, each player $i \in I_k$ computes $x_{i,k+1}$ as the $j_{i,k}$-th iterate of the SA scheme (43), started at $x_{i,k}$ from its outdated profile $y^i_k$, with
--   $$j_{i,k} = \Big\lceil \frac{Q_i}{\eta^{2(k+1)}}\Big\rceil ,\qquad \eta \in (0,1),$$
--   and with sampled gradients that are conditionally unbiased and have conditional second moment at most $M_i^2$ (the hypotheses of Lemma 8); the samples of iteration $k$ are measurable for $\mathcal F_{k+1}$. Players not in $I_k$ keep their strategy. This realizes (38) with $\alpha_{i,k} = \eta^{\beta_{i,k}}$.
--
--   Let $n_0 = \lceil B_2/B_1\rceil$, $\rho = (\max\{a_\infty,\eta\})^{1/(n_0+1)}$, $c = \rho^{1/B_1}$, $q \in (c,1)$, $D \ge 1/\ln((q/c)^e)$, $\epsilon > 0$, and
--   $$\hat\epsilon = \frac{\epsilon}{C + D}\,\rho^{\frac{B_1-1}{B_1}} < 1. \tag{46}$$
--   Let $K = \lceil \ln(1/\hat\epsilon)/\ln(1/q)\rceil$. Then $x_K$ is an $\epsilon$-NE$_\infty$,
--   $$\max_i \mathbb E\big[\|x_{i,K} - x^*_i\|\big] \le \epsilon, \tag{44}$$
--   and the number of projected gradient steps taken by player $i$ during the first $K$ major iterations satisfies
--   $$\sum_{k < K,\ i \in I_k} j_{i,k} \;\le\; \ell^{(1)}_i(\eta) = \frac{Q_i}{\eta^4\ln(1/\eta^2)}\Big(\frac{1}{\hat\epsilon}\Big)^{\frac{\ln(1/\eta^2)}{\ln(1/q)}} + \Big\lceil\frac{\ln(1/\hat\epsilon)}{\ln(1/q)}\Big\rceil . \tag{45}$$
--
--   This is the overall iteration complexity of the asynchronous scheme: with bounded delays and a bounded update window, each player reaches an $\epsilon$-Nash equilibrium in the $\infty$-norm sense after a number of stochastic gradient steps polynomial in $1/\epsilon$, with an exponent governed by $\rho$.
--
--   **Formalization Note** Repairs and implicit hypotheses: the delays are deterministic (the page allows random delays, which its proof does not cover); the oracle's second-moment hypothesis is the bound $\le M_i^2$, not the literal equality of Lemma 8; $C \ge 0$ and $\hat\epsilon < 1$ are assumed (otherwise $\ln(1/\hat\epsilon) \le 0$); "$D \ge / \ln((q/c)^e)$" on the page is read as $D \ge 1/\ln((q/c)^e) = 1/(e\ln(q/c))$, as in Lemma 7. The step count is summed over the update times $k < K$ with $i \in I_k$, which is what player $i$ actually performs (the page's proof bounds the larger sum over all $k < K$). The $\sigma$-algebras $\mathcal G$ of the inner loops are parameters with $\mathcal F_k \subseteq \mathcal G_{i,k,1} \subseteq \mathcal G_{i,k,2} \subseteq \cdots$, $\mathcal G_{i,k,t} \subseteq \mathcal F_{k+1}$ for $t \le j_{i,k}$, and $\xi^t_{i,k}$ measurable for $\mathcal G_{i,k,t+1}$. The ceilings are natural-number ceilings, positive because $\hat\epsilon < 1$ and $q < 1$. The page's special case $B_1 = 1$, $B_2 = 0$ is not stated.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 19, Theorem 3, (44)–(46) and its proof

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm

namespace LeiBR.Async

open MeasureTheory

/-- Theorem 3 (§5.3, p. 19), overall iteration complexity of the asynchronous inexact proximal BR
scheme. Algorithm 3 runs on the deterministic schedule `I` with deterministic delays `τ`
(Assumption 4); player `i ∈ I_k` computes `x_{i,k+1}` as the `j_{i,k} = ⌈Q_i/η^{2(k+1)}⌉`-th iterate of
(43) started at `x_{i,k}` from the outdated profile `y^i_k`, with conditionally unbiased samples of
conditional second moment at most `M_i²`; idle players keep their strategy. Assume Assumptions 1 and 5,
`η ∈ (0, 1)`, `C ≥ 0` and `E‖x_{i,0} − x*_i‖² ≤ C²`. Let `ρ = (max{a_∞, η})^{1/(n₀+1)}`, `n₀ = ⌈B₂/B₁⌉`,
`c = ρ^{1/B₁}`, `q ∈ (c, 1)`, `D ≥ 1/ln((q/c)^e)`, `ϵ > 0` and `ϵ̂ = ϵ ρ^{(B₁−1)/B₁}/(C + D) < 1`.
After `K = ⌈ln(1/ϵ̂)/ln(1/q)⌉` major iterations, `x_K` is an `ϵ`-NE∞ (`max_i E‖x_{i,K} − x*_i‖ ≤ ϵ`), and
player `i` has taken at most `ℓ^{(1)}_i(η)` projected gradient steps, (45). -/
theorem theorem_3 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N d : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i)) (f : Fin N → LeiBR.Sync.Profile n → ℝ)
    (ψ : Fin N → LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i, LeiBR.Sync.Profile n → EuclideanSpace ℝ (Fin d) → LeiBR.Sync.Strat n i)
    (ξ0 : Ω → EuclideanSpace ℝ (Fin d)) (M : Fin N → ℝ)
    (hA1 : Assumption1 P X f ψ gψ ξ0 M) (hgψ : ∀ i, Measurable (Function.uncurry (gψ i)))
    (μ : ℝ) (hμ : 0 < μ) (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : LeiBR.Sync.IsProxBR X f μ xhat)
    (xs : LeiBR.Sync.Profile n) (hNE : LeiBR.Sync.IsNashEq X f xs) (hA5 : Assumption5 X f)
    (I : ℕ → Finset (Fin N)) (τ : Fin N → Fin N → ℕ → ℕ) (B1 B2 : ℕ)
    (hA4 : Assumption4 I τ B1 B2) (hτk : ∀ i j k, τ i j k ≤ k) (hτii : ∀ i k, τ i i k = 0)
    (proj : ∀ i, LeiBR.Sync.Strat n i → LeiBR.Sync.Strat n i)
    (hproj : ∀ i, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (F : Filtration ℕ mΩ) (G : Fin N → ℕ → ℕ → MeasurableSpace Ω)
    (ξs : Fin N → ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hFG : ∀ i k, F k ≤ G i k 1) (hGmono : ∀ i k t, G i k t ≤ G i k (t + 1))
    (hGF : ∀ i k t, t ≤ jSteps (LeiBR.Sync.Qconst X M μ) η i k → G i k t ≤ F (k + 1))
    (hξ : ∀ i k t, Measurable[G i k (t + 1)] (ξs i k t))
    (x : ℕ → Ω → LeiBR.Sync.Profile n) (hx0X : ∀ ω, x 0 ω ∈ profileSet X) (hx0 : Measurable[F 0] (x 0))
    (hstep : ∀ k ω i, x (k + 1) ω i =
      if i ∈ I k then
        saPath proj gψ μ i (delayed x τ i k ω) (fun t => ξs i k t ω) (jSteps (LeiBR.Sync.Qconst X M μ) η i k)
      else x k ω i)
    (horacle : ∀ k, ∀ i ∈ I k, IsSAOracle P f gψ proj μ M i (delayed x τ i k) (ξs i k) (G i k)
      (jSteps (LeiBR.Sync.Qconst X M μ) η i k))
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ i, ∫ ω, ‖x 0 ω i - xs i‖ ^ 2 ∂P ≤ C ^ 2)
    (ρ c q D ϵ : ℝ) (hρ : ρ = rhoAsync (normInf (LeiBR.Sync.Gamma X f μ)) η B1 B2)
    (hc : c = ρ ^ (1 / (B1 : ℝ))) (hcq : c < q) (hq1 : q < 1)
    (hD : 1 / (Real.exp 1 * Real.log (q / c)) ≤ D) (hϵ : 0 < ϵ)
    (hϵhat : epsHat ϵ C D ρ B1 < 1) :
    (∀ i, ∫ ω, ‖x ⌈Real.log (1 / epsHat ϵ C D ρ B1) / Real.log (1 / q)⌉₊ ω i - xs i‖ ∂P ≤ ϵ) ∧
      ∀ i, (∑ k ∈ (Finset.range ⌈Real.log (1 / epsHat ϵ C D ρ B1) / Real.log (1 / q)⌉₊).filter
          (fun k => i ∈ I k), (jSteps (LeiBR.Sync.Qconst X M μ) η i k : ℝ)) ≤
        ellOne (LeiBR.Sync.Qconst X M μ i) η q (epsHat ϵ C D ρ B1) := by sorry

end LeiBR.Async
