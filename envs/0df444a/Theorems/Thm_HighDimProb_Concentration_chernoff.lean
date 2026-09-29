-- Prove2me | Theorems.Thm_HighDimProb_Concentration_chernoff
-- name    : HighDimProb.Concentration.chernoff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T05:36:11.389933+00:00
-- url     : https://prove2.me/theorems/fedb593d-65e6-4ab0-bd1a-2545a5d67839
-- title:
--   Theorem 2.3.1 — Chernoff's inequality
-- statement:
--   This is **Chernoff's inequality** for a sum of independent Bernoulli random variables
--   with possibly different parameters.
--
--   Let $(\Omega, \mathcal F, P)$ be a probability space, and let $X_1, \dots, X_N : \Omega
--   \to \mathbb R$ be independent random variables with $X_i$ taking the value $1$ with
--   probability $p_i$ and $0$ with probability $1 - p_i$ (a Bernoulli distribution with
--   parameter $p_i$, not necessarily identical across $i$). Write $S_N = \sum_{i=1}^N X_i$
--   for their sum and $\mu = \mathbb E S_N$ for its mean. Then, for every $t > \mu$,
--
--   $$
--   P\{S_N \ge t\} \;\le\; e^{-\mu}\left(\frac{e\mu}{t}\right)^{t}.
--   $$
--
--   Unlike Hoeffding's inequality, this bound is sensitive to the magnitude of the parameters
--   $p_i$: it is sharp when the $S_N$ is nearly Poisson (small $p_i$, large $N$), a regime
--   where Hoeffding's Gaussian-shaped tail is far too conservative.
--
--   **Formalization Note** The Bernoulli hypothesis is stated directly via the two
--   point-probabilities $P\{X_i = 1\} = p_i$ and $P\{X_i = 0\} = 1 - p_i$, which forces
--   $X_i \in \{0, 1\}$ almost surely and $\mu = \sum_i p_i$; no separate constraint
--   $p_i \in [0,1]$ is needed, since it follows automatically from these being probabilities.
--   The right-hand side uses `Real.rpow` (`^` on `ℝ → ℝ → ℝ`) for the real exponent $t$, exactly
--   as the book's own $t^t$-shaped bound requires.
-- source:
--   Vershynin, High-Dimensional Probability (2018), Theorem 2.3.1, p. 19 (PDF p. 27)

import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace HighDimProb.Concentration

/-- **Theorem 2.3.1** (Chernoff's inequality), Vershynin, *High-Dimensional Probability*
(2018), p. 19.

Let `X₁, …, X_N` be independent Bernoulli random variables with parameters `p₁, …, p_N`.
Consider their sum `S_N = ∑ᵢ Xᵢ` and denote its mean by `μ = E S_N`. Then, for any `t > μ`,

`P {S_N ≥ t} ≤ e^{−μ} (eμ / t)^t`. -/
theorem chernoff {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X P) (p : Fin N → ℝ)
    (hX_ber : ∀ i, P.real {ω | X i ω = 1} = p i ∧ P.real {ω | X i ω = 0} = 1 - p i)
    {t : ℝ} (ht : (∫ ω, ∑ i, X i ω ∂P) < t) :
    P.real {ω | t ≤ ∑ i, X i ω} ≤
      Real.exp (-(∫ ω, ∑ i, X i ω ∂P)) *
        (Real.exp 1 * (∫ ω, ∑ i, X i ω ∂P) / t) ^ t := by sorry

end HighDimProb.Concentration
