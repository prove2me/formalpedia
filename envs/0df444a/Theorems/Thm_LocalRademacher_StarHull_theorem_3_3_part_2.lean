-- Prove2me | Theorems.Thm_LocalRademacher_StarHull_theorem_3_3_part_2
-- name    : LocalRademacher.StarHull.theorem_3_3_part_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T11:28:44.617178+00:00
-- url     : https://prove2.me/theorems/857d107e-9670-4345-abc9-c453ad06e14b
-- title:
--   Theorem 3.3 (part 2, corrected constants), p. 10 — w.p. 1 − e^{−x}, Pf ≤ max{Pₙf, K/(K−1)·Pₙf} + 7.04K r*/B + x(21(b−a) + 6.4BK)/n
-- statement:
--   Let $(\mathcal X, P)$ be a probability space, $n \ge 1$, and $X_1, \dots, X_n$ independent random variables with law $P$. Write $Pf = \mathbb E f(X)$ and $P_n f = \frac1n \sum_{i=1}^n f(X_i)$, and let $\mathbb E R_n \mathcal G$ be the Rademacher average of a class $\mathcal G$, the expectation over the sample of $\frac1n \mathbb E_\sigma \sup_{g \in \mathcal G} \sum_{i} \sigma_i g(X_i)$ with independent uniform signs $\sigma_i$.
--
--   Let $\mathcal F$ be a countable class of measurable functions with values in $[a, b]$. Assume that:
--   1. there are a functional $T$ and a constant $B > 0$ such that, for every $f \in \mathcal F$,
--   $$
--   0 \le T(f), \qquad \operatorname{Var}[f] \le T(f) \le B\, Pf;
--   $$
--   2. $T(\alpha f) \le \alpha^2 T(f)$ for every $f \in \mathcal F$ and $\alpha \in [0,1]$;
--   3. $\psi$ is a sub-root function with fixed point $r^* > 0$, and for every $r \ge r^*$ the empirical Rademacher average of $\{ f \in \operatorname{star}(\mathcal F, 0) : T(f) \le r\}$ is integrable over the sample and
--   $$
--   \psi(r) \ge B\, \mathbb E R_n \{ f \in \operatorname{star}(\mathcal F, 0) : T(f) \le r \}.
--   $$
--
--   Then for every $K > 1$ and every $x > 0$, with probability at least $1 - e^{-x}$,
--   $$
--   \forall f \in \mathcal F \qquad Pf \le \max\Big\{ P_n f,\ \frac{K}{K-1} P_n f \Big\} + \frac{7.04\, K}{B}\, r^* + \frac{x\,\big(21 (b - a) + 6.4\, B K\big)}{n},
--   $$
--   and, also with probability at least $1 - e^{-x}$,
--   $$
--   \forall f \in \mathcal F \qquad P_n f \le \frac{K+1}{K} Pf + \frac{7.04\, K}{B}\, r^* + \frac{x\,\big(21 (b - a) + 6.4\, B K\big)}{n}.
--   $$
--
--   The complexity of the class enters only through the fixed point $r^*$ of a sub-root bound on local Rademacher averages, rather than through a global Rademacher average. This gives fast rates (of order $r^*$, often $\log n/n$) in settings such as empirical risk minimization with a Bernstein-type variance condition.
--
--   **Formalization Note** The page states the result with $c_1 = 6$, $c_2 = 5$, the term $11(b-a)$, and $\frac{K}{K-1}P_n f$ in the first claim. The proof (pp. 15–17, at the paper's choice $\alpha = 1/10$) yields $c_1 = 4(1+\alpha)^2 + 2(1+\alpha) = 7.04$, $c_2 = 4(1+\alpha) + 2 = 6.4$ and $2(b-a)(1/3 + 1/\alpha) = \tfrac{62}{3}(b-a) \le 21(b-a)$; the display on p. 16 drops the factor $2$ of the term $2C$, and no $\alpha > 0$ gives $(6, 5)$. For $P_n f < 0$ the argument gives $P_n f$, not $\frac{K}{K-1}P_n f$, so the first claim is stated with the maximum, which equals the print when $P_n f \ge 0$. These constants are written as the decimals `7.04` and `6.4` in Lean. Added hypotheses, all implicit on the page: $B > 0$ (Lemma 3.8), $n \ge 1$, $T \ge 0$ on $\mathcal F$ (from $T : \mathcal F \to \mathbb R^+$). The paper's standing assumption that suprema of empirical processes are measurable (p. 7) is encoded by countability and measurability of $\mathcal F$. The failure events are measured by the outer product measure. The integrability of the local empirical Rademacher averages keeps the expectation from being a junk value. $T$ is a functional on all real functions; only its values on $\mathcal F$ are constrained. Part 1 of the theorem is not stated.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Theorem 3.3 (second part), p. 10; proof p. 17 with pp. 14–16; notation p. 3; standing measurability assumption p. 7

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized

namespace LocalRademacher.StarHull

/-- **Theorem 3.3, second part** (p. 10; corrected constants and first claim). Let `P` be a
probability measure on `X`, `n ≥ 1`, and `F` a countable class of measurable functions with
values in `[a, b]` (countability encodes the standing measurability assumption of p. 7). Let
`T` be a functional with `0 ≤ T(f)`, `Var[f] ≤ T(f) ≤ B Pf` on `F`, `B > 0`, and
`T(αf) ≤ α² T(f)` for `f ∈ F`, `α ∈ [0, 1]`. Let `ψ` be sub-root with fixed point `r* > 0`, and
assume that for every `r ≥ r*` the empirical Rademacher average of `{f ∈ star(F, 0) : T(f) ≤ r}`
is integrable over the sample and `ψ(r) ≥ B E Rₙ {f ∈ star(F, 0) : T(f) ≤ r}`. Then for every
`K > 1` and `x > 0`, with probability at least `1 − e^{−x}`, every `f ∈ F` satisfies
`Pf ≤ max{Pₙf, K/(K−1) Pₙf} + 7.04 K r*/B + x (21 (b − a) + 6.4 B K)/n`,
and, with probability at least `1 − e^{−x}`, every `f ∈ F` satisfies
`Pₙf ≤ (K+1)/K Pf + 7.04 K r*/B + x (21 (b − a) + 6.4 B K)/n`.
The page prints `c₁ = 6`, `c₂ = 5`, `11 (b − a)` and `K/(K−1) Pₙf`; the proof (pp. 15–17) gives
`7.04`, `6.4`, `62/3 · (b − a) ≤ 21 (b − a)` at `α = 1/10`, and the maximum for `Pₙf < 0`.
Each failure event is measured by the (outer) product measure. -/
theorem theorem_3_3_part_2 {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n)
    (F : Set (X → ℝ)) (hFc : F.Countable) (hmeas : ∀ f ∈ F, Measurable f)
    (a b : ℝ) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc a b)
    (T : (X → ℝ) → ℝ) (B : ℝ) (hB : 0 < B) (hT0 : ∀ f ∈ F, 0 ≤ T f)
    (hvar : ∀ f ∈ F, variance f P ≤ T f) (hTB : ∀ f ∈ F, T f ≤ B * ∫ x, f x ∂P)
    (hTsq : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (fun x => α * f x) ≤ α ^ 2 * T f)
    (ψ : ℝ → ℝ) (hψ : IsSubRoot ψ) (rstar : ℝ) (hrstar : 0 < rstar) (hfix : ψ rstar = rstar)
    (hloc : ∀ r, rstar ≤ r →
      Integrable (fun s : Fin n → X => empRademacher (localClass F T r) s)
          (Measure.pi fun _ : Fin n => P) ∧
        B * expRademacher P n (localClass F T r) ≤ ψ r)
    (K x : ℝ) (hK : 1 < K) (hx : 0 < x) :
    (Measure.pi fun _ : Fin n => P)
        {s | ∃ f ∈ F, max (empMean s f) (K / (K - 1) * empMean s f)
            + (7.04 : ℝ) * K / B * rstar + x * (21 * (b - a) + (6.4 : ℝ) * B * K) / n
            < ∫ y, f y ∂P}
        ≤ ENNReal.ofReal (Real.exp (-x)) ∧
      (Measure.pi fun _ : Fin n => P)
        {s | ∃ f ∈ F, (K + 1) / K * (∫ y, f y ∂P)
            + (7.04 : ℝ) * K / B * rstar + x * (21 * (b - a) + (6.4 : ℝ) * B * K) / n
            < empMean s f}
        ≤ ENNReal.ofReal (Real.exp (-x)) := by sorry

end LocalRademacher.StarHull
