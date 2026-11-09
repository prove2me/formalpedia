-- Prove2me | Theorems.Thm_KTaxi_Competitive_theorem_2_1
-- name    : KTaxi.Competitive.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:21.453329+00:00
-- url     : https://prove2.me/theorems/f0183df2-3926-4d82-87c0-820ccba56e1c
-- title:
--   Theorem 2.1 — exponential race: $P(\zeta_i=\min_j\zeta_j)=\lambda_i/\sum_j\lambda_j$
-- statement:
--   Let $\zeta_1,\dots,\zeta_m$ be independent real random variables on a probability space, with $\zeta_i\sim\mathrm{Exp}(\lambda_i)$ and $\lambda_i>0$. Then for every $i$,
--   $$
--   P\Bigl(\zeta_i=\min_{1\le j\le m}\zeta_j\Bigr)=\frac{\lambda_i}{\sum_{j=1}^m\lambda_j}.
--   $$
--   Among independent exponential random variables, the probability that a given one is the smallest is proportional to its rate. It gives the selection probabilities $w_i/(d_iZ_m)$ of Algorithm 1.
--
--   **Formalization Note** The variables are measurable maps `ζ : Fin m → Ω → ℝ` with `iIndepFun ζ P` and `P.map (ζ i) = expMeasure (rate i)`. The event is $\{\omega:\zeta_i(\omega)\le\zeta_j(\omega)\ \forall j\}$, and the probability is compared in `ℝ≥0∞`.
--
--   Differences from the source:
--   - encoding: ζ_i = min_j ζ_j → ζ_i ≤ ζ_j for every j; reason: the same event
--   - encoding: indices 1, …, m → Fin m (0-based); reason: Lean convention; same instances
-- source:
--   Christian Coester, Yichen Huang, Tze-Yang Poon, The k-Taxi Problem Is Competitive on All Metrics, STOC 2027 submission #96 (October 2026; PDF SHA-256 09242267e431f586117500ee75c63e6f203519f497d01ee4d90d6989341648ed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/96.pdf, Theorem 2.1, PDF p. 4 (printed p. 3)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace KTaxi.Competitive

/-- **Theorem 2.1** (exponential race; Coester–Huang–Poon, STOC 2027 #96, PDF p. 4).
Let `ζ₁, …, ζ_m` be independent real random variables on a probability space with
`ζ_i ∼ Exp(λ_i)` and `λ_i > 0`. Then for every `i`,
`P(ζ_i = min_j ζ_j) = λ_i / ∑_j λ_j`. -/
theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m : ℕ} (ζ : Fin m → Ω → ℝ) (rate : Fin m → ℝ) (hrate : ∀ i, 0 < rate i)
    (hmeas : ∀ i, Measurable (ζ i)) (hind : iIndepFun ζ P)
    (hlaw : ∀ i, P.map (ζ i) = expMeasure (rate i)) (i : Fin m) :
    P {ω | ∀ j, ζ i ω ≤ ζ j ω} = ENNReal.ofReal (rate i / ∑ j, rate j) := by sorry

end KTaxi.Competitive
