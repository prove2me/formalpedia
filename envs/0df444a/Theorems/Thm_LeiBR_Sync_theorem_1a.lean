-- Prove2me | Theorems.Thm_LeiBR_Sync_theorem_1a
-- name    : LeiBR.Sync.theorem_1a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:31.870635+00:00
-- url     : https://prove2.me/theorems/8e846962-6731-462e-8681-9bffd84200bb
-- title:
--   Theorem 1(a) — synchronous inexact proximal BR reaches an $\epsilon$-NE$_2$ within $\ell_i(\eta)$ projected SG steps per player
-- statement:
--   Consider the $N$-player stochastic Nash game under Assumptions 1 and 2, with $\mu>0$, a Nash equilibrium $x^*$, and $Q_i=2M_i^2/\mu^2+2D_{X_i}^2$. Run Algorithm 1 from a deterministic $x_0\in X$ with $\|x_{i,0}-x_i^*\|\le C$, computing each inexact proximal BR by the inner loop (SA$_{i,k}$) with
--   $$j_{i,k}=\Big\lceil\frac{Q_i}{\eta^{2(k+1)}}\Big\rceil$$
--   projected stochastic gradient steps at major iteration $k$, for some $\eta\in(0,1)$ (so that (8) holds with $\alpha_{i,k}=\eta^{k+1}$). The sampled gradients satisfy the hypotheses of Lemma 3 at every $(k,i,t)$ with $1\le t\le j_{i,k}$, and the sampled gradient map and the samples are measurable.
--
--   Let $a=\|\Gamma\|$, $c=\max\{a,\eta\}$, $q\in(c,1)$, $D=1/\ln((q/c)^e)$, $0<\epsilon<\sqrt N(C+D)$, and run
--   $$K=\Big\lceil\frac{\ln\big(\sqrt N(C+D)/\epsilon\big)}{\ln(1/q)}\Big\rceil$$
--   major iterations. Then:
--   1. $x_K$ is an $\epsilon$-NE$_2$ in the sense of (26): $\mathbb E\big\|(\|x_{1,K}-x_1^*\|,\dots,\|x_{N,K}-x_N^*\|)\big\|\le\epsilon$;
--   2. for every player $i$, the number of projected stochastic gradient steps used, $\sum_{k=0}^{K-1}j_{i,k}$, is at most
--   $$\ell_i(\eta)=\frac{Q_i}{\eta^4\ln(1/\eta^2)}\left(\frac{\sqrt N(C+D)}{\epsilon}\right)^{\frac{\ln(1/\eta^2)}{\ln(1/q)}}+\left\lceil\frac{\ln\big(\sqrt N(C+D)/\epsilon\big)}{\ln(1/q)}\right\rceil .$$
--
--   This is the paper's overall iteration complexity of the synchronous scheme: an $\epsilon$-Nash equilibrium is reached with a number of sampled gradients per player that is explicit in $\epsilon$, $N$, $\eta$ and the game's constants.
--
--   **Formalization Note** The theorem states exactly what the proof establishes, (29) and the bound after (31), for the step counts $j_{i,k}$ and the iteration count $K$ used there. Statement repairs: the initial point is deterministic (Algorithm 1), so $\mathbb E\|x_{i,0}-x_i^*\|\le C$ reads $\|x_{i,0}-x^*_i\|\le C$; $\epsilon<\sqrt N(C+D)$ is assumed, since otherwise the ceiling in (27) can be non-positive while no step is taken; the second-moment hypothesis of Lemma 3 is the bound $M_i^2$; Assumption 1(b) is joint $C^2$. $D=1/(e\ln(q/c))$.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 11, Theorem 1(a), (26)–(27); proof p. 12, (29)–(31)

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_LeiBR_Sync_NashGame
import Definitions.Def_LeiBR_Sync_StochGame
import Definitions.Def_LeiBR_Sync_Algorithm1

open MeasureTheory

namespace LeiBR.Sync

/-- Theorem 1(a), p. 11 (overall iteration complexity of the synchronous scheme). Run Algorithm 1
with the inner loop (SA_{i,k}), `j_{i,k} = ⌈Q_i/η^{2(k+1)}⌉` projected stochastic-gradient steps
for player `i` at major iteration `k` (so `α_{i,k} = η^{k+1}`, `η ∈ (0, 1)`), from a
deterministic `x_0 ∈ X` with `‖x_{i,0} - x*_i‖ ≤ C`, for
`K = ⌈ln(√N(C+D)/ϵ)/ln(1/q)⌉` major iterations, where `a = ‖Γ‖`, `c = max{a, η}`,
`q ∈ (c, 1)`, `D = 1/ln((q/c)^e)` and `0 < ϵ < √N(C+D)`. Then `x_K` is an `ϵ`-NE₂,
`E‖(‖x_{i,K} - x*_i‖)_i‖ ≤ ϵ`, and for every player the total number of steps
`∑_{k<K} j_{i,k}` is at most
`ℓ_i(η) = Q_i/(η⁴ ln(1/η²)) · (√N(C+D)/ϵ)^{ln(1/η²)/ln(1/q)} + ⌈ln(√N(C+D)/ϵ)/ln(1/q)⌉`. -/
theorem theorem_1a
    {N : ℕ} {n : Fin N → ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (ξ : Ω → EuclideanSpace ℝ (Fin d))
    (X : ∀ i : Fin N, Set (Strat n i)) (ψ : Fin N → Profile n → EuclideanSpace ℝ (Fin d) → ℝ)
    (gψ : ∀ i : Fin N, Profile n → EuclideanSpace ℝ (Fin d) → Strat n i) (M : Fin N → ℝ)
    (hA1 : Assumption1 P ξ X ψ gψ M) (μ : ℝ) (hμ : 0 < μ)
    (hA2 : Assumption2 X (payoff P ξ ψ) μ)
    (xhat : Profile n → Profile n) (hxhat : IsProxBR X (payoff P ξ ψ) μ xhat)
    (proj : ∀ i : Fin N, Strat n i → Strat n i)
    (hproj : ∀ i : Fin N, SpectralProjGrad.Shared.IsProjOnto (X i) (proj i))
    (hgψ : ∀ i : Fin N,
      Measurable (fun p : Profile n × EuclideanSpace ℝ (Fin d) => gψ i p.1 p.2))
    (j : Fin N → ℕ → ℕ) (ξs : ℕ → Fin N → ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hξs : ∀ k (i : Fin N) t, Measurable (ξs k i t))
    (x0 : Profile n) (hx0 : x0 ∈ stratSet X)
    (xs : Profile n) (hxs : IsNashEq X (payoff P ξ ψ) xs)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hj : ∀ (i : Fin N) (k : ℕ), j i k = ⌈Qconst X M μ i / η ^ (2 * (k + 1))⌉₊)
    (hint : ∀ k (i : Fin N) (t : ℕ), 1 ≤ t → t ≤ j i k →
      Integrable (fun ω => ‖gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
        (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω)‖ ^ 2) P)
    (hunb : ∀ k (i : Fin N) (t : ℕ), 1 ≤ t → t ≤ j i k →
      P[fun ω => gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
          (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω) | innerField j ξs k i t]
        =ᵐ[P] fun ω => partialGrad (payoff P ξ ψ) i
          (Function.update (syncSA proj gψ μ j ξs x0 k ω) i (saZ proj gψ μ j ξs x0 k i t ω)))
    (hvar : ∀ k (i : Fin N) (t : ℕ), 1 ≤ t → t ≤ j i k →
      P[fun ω => ‖gψ i (Function.update (syncSA proj gψ μ j ξs x0 k ω) i
          (saZ proj gψ μ j ξs x0 k i t ω)) (ξs k i t ω)‖ ^ 2 | innerField j ξs k i t]
        ≤ᵐ[P] fun _ => M i ^ 2)
    (C : ℝ) (hC : ∀ i : Fin N, ‖x0 i - xs i‖ ≤ C)
    (q : ℝ) (hcq : max (specNorm (Gamma X (payoff P ξ ψ) μ)) η < q) (hq1 : q < 1)
    (D : ℝ) (hD : D = 1 / (Real.exp 1 *
      Real.log (q / max (specNorm (Gamma X (payoff P ξ ψ) μ)) η)))
    (ϵ : ℝ) (hϵ0 : 0 < ϵ) (hϵ1 : ϵ < Real.sqrt N * (C + D))
    (K : ℕ) (hK : K = ⌈Real.log (Real.sqrt N * (C + D) / ϵ) / Real.log (1 / q)⌉₊) :
    ∫ ω, blockDist (syncSA proj gψ μ j ξs x0 K ω) xs ∂P ≤ ϵ ∧
      ∀ i : Fin N, ∑ k ∈ Finset.range K, (j i k : ℝ) ≤
        Qconst X M μ i / (η ^ 4 * Real.log (1 / η ^ 2)) *
            (Real.sqrt N * (C + D) / ϵ) ^ (Real.log (1 / η ^ 2) / Real.log (1 / q)) +
          (⌈Real.log (Real.sqrt N * (C + D) / ϵ) / Real.log (1 / q)⌉₊ : ℝ) := by sorry

end LeiBR.Sync
