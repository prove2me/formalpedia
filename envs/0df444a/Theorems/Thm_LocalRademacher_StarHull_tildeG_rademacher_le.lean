-- Prove2me | Theorems.Thm_LocalRademacher_StarHull_tildeG_rademacher_le
-- name    : LocalRademacher.StarHull.tildeG_rademacher_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:28:35.539694+00:00
-- url     : https://prove2.me/theorems/bb227df6-0146-4bcc-a562-7a5923e61c05
-- title:
--   Proof of Theorem 3.3 (second part), p. 17 — hence E Rₙ G̃ᵣ ≤ ψ(r)/B
-- statement:
--   Let $(\mathcal X, P)$ be a probability space, $n \ge 1$, and $X_1, \dots, X_n$ independent with law $P$. Let $\mathcal F$ be a countable class of measurable functions with values in $[a,b]$, let $B > 0$ and $r > 0$, and let $T$ be a functional with $T(f) \ge 0$ and $T(\alpha f) \le \alpha^2 T(f)$ for all $f \in \mathcal F$ and $\alpha \in [0,1]$. For a class $\mathcal G$ write
--   $$
--   \mathbb E_\sigma R_n \mathcal G = \frac1n\, \mathbb E_\sigma \sup_{g \in \mathcal G} \sum_{i=1}^n \sigma_i g(X_i)
--   $$
--   for the empirical Rademacher average ($\sigma_i$ independent uniform signs) and $\mathbb E R_n \mathcal G$ for its expectation over the sample.
--
--   Suppose that the empirical Rademacher average of $\mathcal F_r = \{ f \in \operatorname{star}(\mathcal F, 0) : T(f) \le r\}$ is integrable over the sample and that
--   $$
--   B\, \mathbb E R_n \mathcal F_r \le \psi(r).
--   $$
--   Then the empirical Rademacher average of $\tilde{\mathcal G}_r = \{ r f/(T(f)\vee r) : f \in \mathcal F\}$ is integrable over the sample, and
--   $$
--   \mathbb E R_n \tilde{\mathcal G}_r \le \frac{\psi(r)}{B}.
--   $$
--
--   This is the complexity bound that enters the concentration step of the proof of Theorem 3.3 (part 2).
--
--   **Formalization Note** The average over signs is the average over all $2^n$ sign vectors of a real supremum, with no absolute value (the published `empRademacher`). Countability and measurability of $\mathcal F$ encode the paper's standing assumption (p. 7) that suprema of empirical processes are measurable; the integrability hypothesis prevents the expectation from being a junk value $0$.
-- source:
--   Bartlett, Bousquet & Mendelson, arXiv:math/0508275v1, Proof of Theorem 3.3, second part, p. 17, second sentence ("and thus"); notation p. 3; standing assumption p. 7

import Mathlib
import Definitions.Def_VarianceRegularization_Localized_LocalizedComplexity
import Definitions.Def_VarianceRegularization_Localized_RobustRisk
import Definitions.Def_LocalRademacher_StarHull_Classes

open MeasureTheory ProbabilityTheory VarianceRegularization.Localized

namespace LocalRademacher.StarHull

/-- **Rademacher average of the rescaled class** (Proof of Theorem 3.3, second part, p. 17:
"and thus `E Rₙ G̃ᵣ ≤ ψ(r)/B`"). Let `F` be a countable class of measurable functions with values
in `[a, b]` (the standing measurability assumption of p. 7), `n ≥ 1`, `B > 0`, `r > 0`, and `T`
a functional, nonnegative on `F`, with `T(αf) ≤ α² T(f)` for `f ∈ F`, `α ∈ [0, 1]`. If the
empirical Rademacher average of `{f ∈ star(F, 0) : T(f) ≤ r}` is integrable over the sample and
`B · E Rₙ {f ∈ star(F, 0) : T(f) ≤ r} ≤ ψ(r)`, then the empirical Rademacher average of `G̃ᵣ` is
integrable and `E Rₙ G̃ᵣ ≤ ψ(r)/B`. -/
theorem tildeG_rademacher_le {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 0 < n) (F : Set (X → ℝ)) (hFc : F.Countable)
    (hmeas : ∀ f ∈ F, Measurable f) (a b : ℝ) (hrange : ∀ f ∈ F, ∀ x, f x ∈ Set.Icc a b)
    (T : (X → ℝ) → ℝ) (B : ℝ) (hB : 0 < B) (hT0 : ∀ f ∈ F, 0 ≤ T f)
    (hTsq : ∀ f ∈ F, ∀ α ∈ Set.Icc (0 : ℝ) 1, T (fun x => α * f x) ≤ α ^ 2 * T f)
    (ψ : ℝ → ℝ) (r : ℝ) (hr : 0 < r)
    (hint : Integrable (fun s : Fin n → X => empRademacher (localClass F T r) s)
      (Measure.pi fun _ : Fin n => P))
    (hloc : B * expRademacher P n (localClass F T r) ≤ ψ r) :
    Integrable (fun s : Fin n → X => empRademacher (tildeG F T r) s)
        (Measure.pi fun _ : Fin n => P) ∧
      expRademacher P n (tildeG F T r) ≤ ψ r / B := by sorry

end LocalRademacher.StarHull
