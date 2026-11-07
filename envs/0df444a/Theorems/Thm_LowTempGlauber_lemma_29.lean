-- Prove2me | Theorems.Thm_LowTempGlauber_lemma_29
-- name    : LowTempGlauber.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:27:02.842187+00:00
-- url     : https://prove2.me/theorems/86de74db-8af9-4572-89de-64566858a47d
-- title:
--   Lemma 29 — the two-periodic hard-core fixed point $(\alpha,\beta)$: uniqueness, $(d-1)^2\alpha\beta/((1-\alpha)(1-\beta))<1-\zeta$ and $\alpha-\beta\ge\zeta$
-- statement:
--   Let $d\ge3$ and $\lambda>\lambda_c(d)$. There is a constant $\zeta>0$ such that for every $s\ge0$ the system
--   $$\frac{\alpha}{1-\alpha}=\lambda e^{s}\Bigl(\frac{1-\alpha-\beta}{1-\alpha}\Bigr)^d,\qquad\frac{\beta}{1-\beta}=\lambda e^{-s}\Bigl(\frac{1-\alpha-\beta}{1-\beta}\Bigr)^d\tag{44}$$
--   in $\alpha,\beta\ge0$ with $\alpha+\beta\le1$ has a unique solution with $1>\alpha>\beta>0$, and this solution satisfies
--   $$(d-1)^2\frac{\alpha\beta}{(1-\alpha)(1-\beta)}<1-\zeta\qquad\text{and}\qquad\alpha-\beta\ge\zeta.$$
--
--   The solution gives the typical occupation densities of the two sides in the plus phase; the first inequality makes the disagreement exploration subcritical and the second separates the plus phase from balanced sets, the two facts behind Theorem 6.
--
--   **Formalization Note** $\zeta$ is chosen before $s$, so it is uniform over $s\ge0$.
--
--   Differences from the source: none.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Lemma 29, p.34

import Mathlib
import Definitions.Def_LowTempGlauber_HardCore

namespace LowTempGlauber

/-- Galanis–Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission (manuscript sha256 c41a38ff…), Lemma 29, p.34.

Let `d ≥ 3` and `λ > λ_c(d)`. There is a constant `ζ > 0` such that for all `s ≥ 0` the system (44)
`α/(1 − α) = λe^{s}((1 − α − β)/(1 − α))^d`, `β/(1 − β) = λe^{−s}((1 − α − β)/(1 − β))^d`,
for `α, β ≥ 0` with `α + β ≤ 1`, has a unique solution with `1 > α > β > 0`, and it satisfies
`(d − 1)² αβ/((1 − α)(1 − β)) < 1 − ζ` and `α − β ≥ ζ`.

**Formalization Note.** `ζ` is chosen before `s`, so it is uniform in `s ≥ 0`. The pair `(α, β)` is
`p : ℝ × ℝ`; all denominators are positive on the solution set (`α, β < 1`). -/
theorem lemma_29 (d : ℕ) (hd : 3 ≤ d) (lam : ℝ) (hlam : lamC d < lam) :
    ∃ ζ : ℝ, 0 < ζ ∧ ∀ s : ℝ, 0 ≤ s →
      let Sol : ℝ × ℝ → Prop := fun p =>
        0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 ∧
          p.1 / (1 - p.1) = lam * Real.exp s * ((1 - p.1 - p.2) / (1 - p.1)) ^ d ∧
          p.2 / (1 - p.2) = lam * Real.exp (-s) * ((1 - p.1 - p.2) / (1 - p.2)) ^ d ∧
          p.1 < 1 ∧ p.2 < p.1 ∧ 0 < p.2
      (∃! p : ℝ × ℝ, Sol p) ∧
        ∀ p : ℝ × ℝ, Sol p →
          ((d : ℝ) - 1) ^ 2 * (p.1 * p.2 / ((1 - p.1) * (1 - p.2))) < 1 - ζ ∧
            ζ ≤ p.1 - p.2 := by sorry

end LowTempGlauber
