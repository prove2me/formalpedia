-- Prove2me | Theorems.Thm_GlivenkoCantelli_glivenko_cantelli
-- name    : GlivenkoCantelli.glivenko_cantelli
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-05T01:52:07.004713+00:00
-- url     : https://prove2.me/theorems/e94578e6-7a6b-4d8e-ba86-23332e9fe614
-- title:
--   Glivenko–Cantelli theorem: $\sup_{x} |F_n(x) - F(x)| \to 0$ almost surely
-- statement:
--   This is the Glivenko–Cantelli theorem, often called the *fundamental theorem of statistics*: the empirical distribution function of an i.i.d. sample converges to the true distribution function uniformly over the whole real line, with probability one.
--
--   Let $X_1, X_2, \dots$ be independent real-valued random variables on a probability space $(\Omega, \mathcal F, P)$, all with the same distribution, and let
--
--   $$
--   F(x) = P(X_1 \le x), \qquad x \in \mathbb R,
--   $$
--
--   be their common distribution function. For $n \ge 1$ the *empirical distribution function* of the first $n$ observations is
--
--   $$
--   F_n(x, \omega) = \frac{1}{n}\, \#\{\, m \in \{1, \dots, n\} : X_m(\omega) \le x \,\} = \frac{1}{n} \sum_{m=1}^{n} \mathbf 1_{\{X_m(\omega) \le x\}},
--   $$
--
--   the observed frequency of the values not exceeding $x$. Then, for $P$-almost every $\omega$,
--
--   $$
--   \sup_{x \in \mathbb R} \bigl| F_n(x, \omega) - F(x) \bigr| \longrightarrow 0 \qquad (n \to \infty).
--   $$
--
--   No assumption is placed on $F$: it may be any distribution function on $\mathbb R$, with or without atoms.
--
--   The theorem upgrades the pointwise almost-sure convergence $F_n(x) \to F(x)$ for each fixed $x$ (an instance of the strong law of large numbers) to convergence that is uniform in $x$. It is the prototype of a uniform law of large numbers and the starting point of empirical process theory, including the Dvoretzky–Kiefer–Wolfowitz inequality and Vapnik–Chervonenkis theory.
--
--   **Formalization Note** The observations are indexed from $0$: `X i` is $X_{i+1}$. Each `X i` is measurable, the family is mutually independent (`iIndepFun X P`), and every `X i` has the same law as `X 0` (`IdentDistrib (X i) (X 0) P P`). The distribution function $F$ is Mathlib's `cdf (P.map (X 0))`, the distribution function of the law of $X_1$, which equals $P(X_1 \le x)$. The empirical distribution function is the real number `#((Finset.range n).filter (fun i => X i ω ≤ x)) / n`. The supremum is the real `⨆ x : ℝ`; since $0 \le |F_n(x) - F(x)| \le 1$ for all $x$, this is the genuine supremum. For $n = 0$ Lean's convention $0/0 = 0$ gives $F_0 = 0$, which does not affect the limit.
-- source:
--   R. Durrett, Probability: Theory and Examples, 5th ed., Cambridge University Press (2019), Section 2.4, Theorem 2.4.9 (The Glivenko-Cantelli theorem; Theorem 2.4.7 in the 4th ed.): X_1, X_2, ... i.i.d. with distribution F, F_n(x) = n^{-1} sum_{m=1}^n 1(X_m <= x); then sup_x |F_n(x) - F(x)| -> 0 a.s. See also P. Billingsley, Probability and Measure, 3rd ed., Wiley (1995), Section 20, Theorem 20.6 (X_1, X_2, ... independent with common distribution function F, D_n(omega) = sup_x |F_n(x, omega) - F(x)|; then D_n -> 0 with probability 1).

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

namespace GlivenkoCantelli

/-- **The Glivenko–Cantelli theorem** (Durrett, *Probability: Theory and Examples*, 5th ed.,
Theorem 2.4.9; Billingsley, *Probability and Measure*, Theorem 20.6).

Let `X 0, X 1, X 2, …` be independent real random variables on a probability space `(Ω, P)`, all
with the same distribution, and let `F = cdf (P.map (X 0))` be their common distribution function,
`F x = P (X 0 ≤ x)`. The empirical distribution function of the first `n` observations is
`F_n(x) = #{i < n : X i ω ≤ x} / n` (observation `i` here is `X_{i+1}` in the textbooks).
Then, almost surely, `sup_x |F_n(x) - F(x)| → 0` as `n → ∞`.

For every `ω` and `n` the function `x ↦ |F_n(x) - F(x)|` takes values in `[0, 1]`, so the real
`⨆ x` below is the genuine supremum (no junk value is involved). At `n = 0` Lean reads
`F_0 = 0 / 0 = 0`, which does not affect the limit. -/
theorem glivenko_cantelli {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => ⨆ x : ℝ,
        |(((Finset.range n).filter (fun i => X i ω ≤ x)).card : ℝ) / n - cdf (P.map (X 0)) x|)
      atTop (𝓝 0) := by sorry

end GlivenkoCantelli
