-- Prove2me | Theorems.Thm_LeiBR_Async_lemma_7
-- name    : LeiBR.Async.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:07:10.732975+00:00
-- url     : https://prove2.me/theorems/4c116b67-18c7-4ca6-9eeb-966b77b9cf67
-- title:
--   Lemma 7 — geometric rate of the asynchronous inexact proximal BR scheme, (41) and (42)
-- statement:
--   Let Algorithm 3 be applied to the stochastic Nash game with accuracies $\alpha_{i,k} = \eta^{\beta_{i,k}}$ for some $\eta \in (0,1)$, where $\beta_{i,k}$ counts player $i$'s updates up to and including time $k$, and suppose $\mathbb E[\|x_{i,0} - x^*_i\|] \le C$ for every $i$, with $x^*$ a Nash equilibrium. Suppose Assumption 1(a)–(b), Assumption 4 (constants $B_1, B_2$) and Assumption 5 hold, and $\mu > 0$. Let $n_0 = \lceil B_2/B_1\rceil$,
--   $$\rho = \big(\max\{a_\infty, \eta\}\big)^{1/(n_0+1)},\qquad c = \rho^{1/B_1}.$$
--   Then for every $k \ge 0$,
--   $$\max_{i} \mathbb E\big[\|x_{i,k} - x^*_i\|\big] \le (C + k)\,\rho^{\lfloor k/B_1\rfloor}. \tag{41}$$
--   Furthermore, for every $q > c$ and every $D \ge 1/\ln((q/c)^e)$,
--   $$\max_{i} \mathbb E\big[\|x_{i,k} - x^*_i\|\big] \le \rho^{-\frac{B_1-1}{B_1}}\,(C + D)\,q^k\qquad\text{for all } k \ge 0. \tag{42}$$
--
--   The lemma shows that bounded delays and a bounded update window cost only a root in the contraction modulus: the rate per window is $\max\{a_\infty,\eta\}^{1/(n_0+1)}$. It is the rate statement behind the complexity bound of Theorem 3.
--
--   **Formalization Note** The schedule and the delays are deterministic (see the algorithm definition). Only parts (a)–(b) of Assumption 1 are assumed, since the rate does not involve the sampling. Both conclusions are stated as one conjunction; "$\max_i$" is written as a bound for every $i$. $\lfloor k/B_1\rfloor$ is natural-number division and $\rho^{-(B_1-1)/B_1}$ a real power.
-- source:
--   Lei, Shanbhag, Pang & Sen, On Synchronous, Asynchronous, and Randomized Best-Response Schemes for Stochastic Nash Games, arXiv:1704.04578v2, p. 18, Lemma 7, (41)–(42); proof in App. C, pp. 33–35

import Mathlib
import Definitions.Def_LeiBR_Async_Game
import Definitions.Def_LeiBR_Async_Model
import Definitions.Def_LeiBR_Async_Algorithm

namespace LeiBR.Async

open MeasureTheory

/-- Lemma 7 (§5.2, p. 18), geometric rate of the asynchronous scheme. Let Algorithm 3 run with
`α_{i,k} = η^{β_{i,k}}`, `η ∈ (0, 1)`, `E‖x_{i,0} − x*_i‖ ≤ C`, under Assumptions 1, 4 and 5. Let
`ρ = (max{a_∞, η})^{1/(n₀+1)}` with `n₀ = ⌈B₂/B₁⌉` and `c = ρ^{1/B₁}`. Then for all `k ≥ 0`

(41) `max_i E‖x_{i,k} − x*_i‖ ≤ (C + k) ρ^{⌊k/B₁⌋}`, and

(42) for every `q > c` and `D ≥ 1/ln((q/c)^e)`, `max_i E‖x_{i,k} − x*_i‖ ≤ ρ^{−(B₁−1)/B₁}(C + D) q^k`. -/
theorem lemma_7 {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Filtration ℕ mΩ) {N : ℕ} {n : Fin N → ℕ} (X : ∀ i, Set (LeiBR.Sync.Strat n i))
    (f : Fin N → LeiBR.Sync.Profile n → ℝ) (hA1 : Assumption1ab X f) (μ : ℝ) (hμ : 0 < μ)
    (xhat : LeiBR.Sync.Profile n → LeiBR.Sync.Profile n) (hxhat : LeiBR.Sync.IsProxBR X f μ xhat) (xs : LeiBR.Sync.Profile n)
    (hNE : LeiBR.Sync.IsNashEq X f xs) (hA5 : Assumption5 X f) (I : ℕ → Finset (Fin N))
    (τ : Fin N → Fin N → ℕ → ℕ) (B1 B2 : ℕ) (hA4 : Assumption4 I τ B1 B2)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (α : Fin N → ℕ → ℝ) (x : ℕ → Ω → LeiBR.Sync.Profile n)
    (halg : IsAlgorithm3 P F X xhat I τ α x) (hα : ∀ i k, α i k = η ^ updCount I i k)
    (C : ℝ) (hC : ∀ i, ∫ ω, ‖x 0 ω i - xs i‖ ∂P ≤ C)
    (ρ c : ℝ) (hρ : ρ = rhoAsync (normInf (LeiBR.Sync.Gamma X f μ)) η B1 B2)
    (hc : c = ρ ^ (1 / (B1 : ℝ))) :
    (∀ k i, ∫ ω, ‖x k ω i - xs i‖ ∂P ≤ (C + k) * ρ ^ (k / B1)) ∧
      ∀ q D : ℝ, c < q → 1 / (Real.exp 1 * Real.log (q / c)) ≤ D →
        ∀ k i, ∫ ω, ‖x k ω i - xs i‖ ∂P ≤ ρ ^ (-((B1 : ℝ) - 1) / B1) * (C + D) * q ^ k := by sorry

end LeiBR.Async
