-- Prove2me | Theorems.Thm_LargeDeviations_cramer_theorem_real
-- name    : LargeDeviations.cramer_theorem_real
-- status  : Open
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:38:01.21399+00:00
-- url     : https://prove2.me/theorems/238a1f4a-1df0-42a7-86db-41b20700d8e3
-- title:
--   Cramér's theorem in $\mathbb{R}$: exponential decay rate of $\mathbb P(X_1+\dots+X_n\ge na)$
-- statement:
--   This is Cramér's large deviation theorem for sums of i.i.d. real random variables, in its classical half-line form.
--
--   Let $X_1,X_2,\dots$ be independent, identically distributed real random variables on a probability space $(\Omega,\mathcal F,\mathbb P)$ whose logarithmic moment generating function
--   $$\Lambda(t)=\log \mathbb E\big[e^{tX_1}\big]$$
--   is finite for every $t\in\mathbb R$. Let
--   $$I(a)=\sup_{t\in\mathbb R}\big(ta-\Lambda(t)\big).$$
--
--   **Theorem (Cramér).** For every $a\in\mathbb R$ with $\mathbb E X_1<a$ and $\mathbb P(X_1>a)>0$,
--   $$\lim_{n\to\infty}\frac1n\log\mathbb P\big(X_1+\dots+X_n\ge na\big)=-I(a).$$
--
--   The upper bound $\mathbb P(X_1+\dots+X_n\ge na)\le e^{-nI(a)}$ is the Chernoff bound; the content of the theorem is the matching lower bound, usually proved by an exponential change of measure (tilting). Cramér's theorem (1938) is the founding result of large deviations theory and the prototype for Sanov's theorem, the Gärtner–Ellis theorem and the large deviation estimates used in statistics, information theory and queueing. It is the half-line case of the large deviation principle of Dembo–Zeitouni, Theorem 2.2.3.
--
--   **Formalization Note** The variables are indexed from $0$: `X i` is $X_{i+1}$, so `∑ i ∈ Finset.range n, X i ω` is $X_1+\dots+X_n$. Each `X i` is measurable, the family is mutually independent (`iIndepFun X P`), and every `X i` has the same law as `X 0` (`IdentDistrib (X i) (X 0) P P`). Finiteness of $\Lambda$ everywhere is the hypothesis that $\omega\mapsto e^{tX_1(\omega)}$ is integrable for every real $t$; this also makes $X_1$ integrable, so the Bochner integral in the hypothesis $\mathbb E X_1<a$ is the genuine expectation. $\Lambda(t)$ is Mathlib's `cgf (X 0) P t`, which is by definition `Real.log` of the Bochner integral $\int e^{tX_1}\,d\mathbb P$. The probability is the real number `(P {ω | n * a ≤ ∑ i ∈ Finset.range n, X i ω}).toReal` and the logarithm is `Real.log`. Under the hypotheses this probability is at least $\mathbb P(X_1>a)^n>0$ for $n\ge1$, so Lean's junk value $\log 0=0$ never occurs. The rate $I(a)$ is the real supremum `⨆ t : ℝ, (t * a - cgf (X 0) P t)`; under the hypotheses $ta-\Lambda(t)\le-\log\mathbb P(X_1>a)$ for all $t$ (for $t\ge0$ because $\mathbb E e^{tX_1}\ge e^{ta}\,\mathbb P(X_1>a)$, and for $t<0$ by Jensen's inequality and $\mathbb E X_1<a$), so the family is bounded above and this is the genuine finite supremum, not Lean's junk value $0$ for unbounded families. At $n=0$ the factor $1/n$ is $0$ in Lean, so the $n=0$ term is $0$, which does not affect the limit.
-- source:
--   H. Cramér, 'Sur un nouveau théorème-limite de la théorie des probabilités', Actualités Scientifiques et Industrielles 736 (1938), 5–23. R. Durrett, Probability: Theory and Examples, 5th ed., Cambridge University Press, 2019, Section 2.7 (Large deviations). A. Dembo and O. Zeitouni, Large Deviations Techniques and Applications, 2nd ed., Springer, 1998, Section 2.2.1, Theorem 2.2.3 (the large deviation principle in ℝ, of which this is the half-line case).

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeDeviations

/-- **Cramér's theorem in ℝ, half-line form** (Cramér 1938; Durrett, *Probability: Theory and
Examples*, 5th ed., Section 2.7; Dembo–Zeitouni, *Large Deviations Techniques and Applications*,
2nd ed., Theorem 2.2.3 applied to half-lines).

Let `X 0, X 1, …` be i.i.d. real random variables whose moment generating function
`E[exp (t * X 0)]` is finite for every real `t`, so that the log-moment generating function
`Λ t = cgf (X 0) P t = log E[exp (t * X 0)]` is a real number for every `t`. Let
`I a = ⨆ t : ℝ, (t * a - Λ t)`. For every `a` with `E[X 0] < a` and `P (X 0 > a) > 0`,
`(1 / n) * log P (X 0 + ⋯ + X (n - 1) ≥ n * a) → -I a` as `n → ∞`.

Under these hypotheses `P (X 0 + ⋯ + X (n - 1) ≥ n * a) ≥ P (X 0 > a) ^ n > 0` for `n ≥ 1`, so
`Real.log` is the genuine logarithm, and `t * a - Λ t ≤ -log P (X 0 > a)` for all `t`, so the
real `⨆` is the genuine (finite) supremum. At `n = 0` the term is `0`, which does not affect
the limit. -/
theorem cramer_theorem_real {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hfin : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X 0 ω)) P)
    (a : ℝ) (hmean : ∫ ω, X 0 ω ∂P < a) (hpos : 0 < P {ω | a < X 0 ω}) :
    Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) *
        Real.log ((P {ω | (n : ℝ) * a ≤ ∑ i ∈ Finset.range n, X i ω}).toReal))
      atTop (𝓝 (-⨆ t : ℝ, (t * a - cgf (X 0) P t))) := by sorry

end LargeDeviations
