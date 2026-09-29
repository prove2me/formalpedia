-- Prove2me | Theorems.Thm_OnlineNRM_TSFixed_tsFixed_bayesRegret_le
-- name    : OnlineNRM.TSFixed.tsFixed_bayesRegret_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T21:09:22.708266+00:00
-- url     : https://prove2.me/theorems/a1fa757c-68eb-4d4e-b6a1-589c65ab9c89
-- title:
--   Theorem 1 — Bayesian regret of TS-fixed against the LP benchmark
-- statement:
--   Consider the network revenue management model of Section 2.1 with $N$ products, $M$ resources, consumption matrix $a_{ij}\ge0$, initial inventories $I_j\ge0$, $T\ge1$ periods and $K\ge2$ price vectors $p_k$ with nonnegative entries, plus the shut-off price. Let the parameter space $\Theta$ carry an arbitrary prior $\mu_0$, and assume bounded demand: for every parameter and every price vector $p_k$, the demand of product $i$ lies in $[0,\bar d_i]$ almost surely. Let $p_{\max}=\max_k\sum_i p_{ik}\bar d_i$ and $p^j_{\max}=\max_{i:a_{ij}\neq0,\,k}p_{ik}/a_{ij}$.
--
--   Then every run of TS-fixed (Algorithm 1), with any fulfilment rule obeying (a)/(b) of Section 2.1 and any measurable choice of optimal LP solutions, satisfies
--
--   $$
--   \mathbb E\bigl[\mathrm{OPT}(d)\bigr]\cdot T-\mathbb E\bigl[\mathrm{Rev}(T)\bigr]\ \le\ \Bigl(18\,p_{\max}+37\sum_{i=1}^N\sum_{j=1}^M p^j_{\max}\,a_{ij}\,\bar d_i\Bigr)\cdot\sqrt{TK\log K},
--   $$
--
--   where $d=d(\theta)$ is the mean demand under the true parameter, $\mathrm{OPT}(d)$ is the optimal value of $\mathrm{LP}(d)$ with $c_j=I_j/T$, and $\mathrm{Rev}(T)$ is the revenue actually collected (satisfied demand times posted prices).
--
--   The bound is prior-free: the constants depend only on prices, consumption and demand bounds. It shows that Thompson sampling combined with an LP subroutine loses at most $O(\sqrt{TK\log K})$ revenue against the fluid LP relaxation of the known-demand problem.
--
--   **Formalization Note** The paper prints $\mathrm{BayesRegret}(T)=\mathbb E[\mathrm{Rev}^*(T)]-\mathbb E[\mathrm{Rev}(T)]\le(\dots)\sqrt{TK\log K}$ with no restriction on $K$. This states two corrections. (1) **$K\ge2$ is added**: the right-hand side is $0$ at $K=1$ while TS-fixed has regret of order $\sqrt T$ on a one-price instance with Bernoulli demand and $I=T/2$. (2) **The LP benchmark $\mathbb E[\mathrm{OPT}(d)]\cdot T$ replaces $\mathbb E[\mathrm{Rev}^*(T)]$**: under the paper's fulfilment rule (b), $\mathbb E[\mathrm{Rev}^*(T)\mid d]\le\mathrm{OPT}(d)\cdot T$ (Section 3.1.1) fails when products use disjoint resources (two products, $I=(T,1)$, $p_1=(1,0)$, $p_2=(1/2,0)$, deterministic demand $(1,1)$: $\mathrm{Rev}^*\ge T$ while $\mathrm{OPT}(d)\cdot T=1$), so the printed bound fails for large $T$. The paper states that its proof bounds the gap to "the LP benchmark defined in Section 3.1.1" (p. 1594), and the last display of Section 3.1.1 bounds $\mathrm{BayesRegret}(T)$ by exactly this quantity; wherever the Gallego–van Ryzin bound holds (e.g. $N=1$), the corrected statement implies the printed one. The logarithm is natural (the paper does not say; the adapted analyses of Bubeck–Liu 2013 and Russo–Van Roy 2014 use the natural log). Nonnegativity of prices, consumption and inventory is implicit in the paper and stated explicitly. $\Theta$ is a standard Borel space (a Borel subset of $\mathbb R^l$ is one). Periods are 0-based in Lean.
-- source:
--   Ferreira, Simchi-Levi, Wang, Online Network Revenue Management Using Thompson Sampling, Oper. Res. 66(6), 2018, p. 1594, Theorem 1

import Mathlib
import Definitions.Def_OnlineNRM_TSFixed_LP
import Definitions.Def_OnlineNRM_TSFixed_Run

namespace OnlineNRM.TSFixed

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- Theorem 1 of Ferreira, Simchi-Levi and Wang (2018), with `K ≥ 2` and the LP benchmark
`E[OPT(d)] · T` in place of `E[Rev*(T)]`. -/
theorem tsFixed_bayesRegret_le {N M K T : ℕ} (hK : 2 ≤ K) (hT : 1 ≤ T)
    (p : Fin N → Fin K → ℝ) (a : Fin N → Fin M → ℝ) (I : Fin M → ℝ) (dbar : Fin N → ℝ)
    (hp : ∀ i k, 0 ≤ p i k) (ha : ∀ i j, 0 ≤ a i j) (hI : ∀ j, 0 ≤ I j)
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (μ₀ : Measure Θ) [IsProbabilityMeasure μ₀]
    (F : Kernel (Θ × Fin K) (Fin N → ℝ)) [IsMarkovKernel F]
    (hF : ∀ ρ k, ∀ᵐ x ∂(F (ρ, k)), ∀ i, x i ∈ Set.Icc 0 (dbar i))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (θ : Ω → Θ) (θs : ℕ → Ω → Θ) (A : ℕ → Ω → Option (Fin K))
    (D Dsat : ℕ → Ω → Fin N → ℝ) (xsel : Θ → Fin K → ℝ)
    (hrun : IsTSFixedRun p a I F μ₀ T P θ θs A D Dsat xsel) :
    lpBayesRegret p a I F T P θ A Dsat ≤
      (18 * pmax p dbar + 37 * ∑ i : Fin N, ∑ j : Fin M, pjmax p a j * a i j * dbar i) *
        Real.sqrt ((T : ℝ) * K * Real.log K) := by sorry

end OnlineNRM.TSFixed
