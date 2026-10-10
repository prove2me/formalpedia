-- Prove2me | Theorems.Thm_MultiPriceOnline_Hardness_theorem_3
-- name    : MultiPriceOnline.Hardness.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:02.209977+00:00
-- url     : https://prove2.me/theorems/0163c247-9443-4b4b-b18b-a370f0934339
-- title:
--   Theorem 3, p. 17 — no online algorithm earns more than (F(𝒫) + ε) · E[OPT] on some deterministic random instance
-- statement:
--   Let $k \ge 1$ be an integer and let $\mathcal P = \{r^{(1)} < \dots < r^{(m)}\}$, $m \ge 1$, $r^{(1)} > 0$, be a price set with booking limits $\alpha^{(1)}, \dots, \alpha^{(m)}$ (Proposition 1). Write $F(\mathcal P) = 1 - e^{-\alpha^{(1)}}$. For every $\varepsilon > 0$ there exist:
--
--   1. a setup $\mathcal S$ with some number $n$ of items, each with starting inventory $k$ and price set $\mathcal P$;
--   2. a finite probability distribution (weights $w_a \ge 0$ summing to $1$) over arrival sequences $\mathcal A_a$, all in the deterministic case, with $\mathbb E_{\mathcal A}[\mathrm{OPT}(\mathcal S, \mathcal A)] > 0$.
--
--   They satisfy the following: for every randomized online algorithm, that is, every measurable random choice of a deterministic online algorithm on any probability space,
--
--   $$\mathbb E_{\mathcal A}\big[\mathbb E[\mathrm{ALG}(\mathcal S, \mathcal A)]\big] \le \big(F(\mathcal P) + \varepsilon\big)\, \mathbb E_{\mathcal A}\big[\mathrm{OPT}(\mathcal S, \mathcal A)\big].$$
--
--   By Yao's minimax principle, no online algorithm has a competitive ratio above $F(\mathcal P)$ on all setups with price set $\mathcal P$ and inventory $k$, even in the deterministic case. Since $k$ is arbitrary, the guarantees of Theorem 2 and of Corollary 1 are therefore tight.
--
--   **Formalization Note** The paper states the bound with $\varepsilon = 0$. Its proof ignores the rounding of the phase lengths and takes $n \to \infty$ (pp. 23, 47), so it establishes only the $\varepsilon$-form. The $\varepsilon$-form is what the tightness argument via Yao's principle uses. The condition $\mathbb E[\mathrm{OPT}] > 0$ is added because without it an empty arrival sequence would satisfy the statement trivially. The paper's instance has positive OPT. The distribution is fixed before the algorithm. The algorithm may depend on the setup and on its own randomness, but sees only the past and present customers. Measurability of the revenue in $\omega$ is assumed. The revenue is bounded, so it is then integrable; without measurability the Bochner integral would be $0$ and the bound trivially true.
-- source:
--   Ma, Simchi-Levi, Algorithms for Online Matching, Assortment, and Pricing with Tight Weight-dependent Competitive Ratios, arXiv:1905.04770v1, p. 17, Theorem 3; proof p. 25 (§5) and pp. 46–48 (App. D)

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Model

namespace MultiPriceOnline.Hardness
open Finset MeasureTheory
theorem theorem_3 (k : ℕ) (hk : 1 ≤ k) (m : ℕ) (hm : 1 ≤ m) (r : ℕ → ℝ) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (α : ℕ → ℝ) (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (ε : ℝ) (hε : 0 < ε) :
    ∃ n K : ℕ, ∃ w : Fin K → ℝ, ∃ A : Fin K → Arrival n,
      (∀ a, 0 ≤ w a) ∧ (∑ a, w a) = 1 ∧ (∀ a, IsDeterministic (A a)) ∧
      0 < ∑ a, w a * OPT k m r (A a) ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (alg : Ω → OnlineAlg n),
        (∀ a, Measurable (fun ω => revenue k m r (alg ω) (A a))) →
        ∑ a, w a * ∫ ω, revenue k m r (alg ω) (A a) ∂μ
          ≤ (1 - Real.exp (-α 1) + ε) * ∑ a, w a * OPT k m r (A a) := by sorry
end MultiPriceOnline.Hardness
