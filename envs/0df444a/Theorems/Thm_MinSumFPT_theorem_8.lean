-- Prove2me | Theorems.Thm_MinSumFPT_theorem_8
-- name    : MinSumFPT.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:16:37.273193+00:00
-- url     : https://prove2.me/theorems/408796ae-2c9a-43d0-87d2-aacc49a47e17
-- title:
--   Theorem 8 — sublinear $(1\pm\varepsilon)$ estimate of $\mathrm{cost}(X)$
-- statement:
--   There is a single randomized program, taking $n,\varepsilon,\delta$ as input, and a constant $C$ such that for all $n\ge1$, $\varepsilon,\delta\in(0,1)$ and every pseudometric $d$ on an $n$-point set $X$:
--
--   1. on every random tape it halts within $C\cdot\varepsilon^{-2}\cdot n\cdot\log_2(2+1/\delta)$ steps;
--   2. with probability at least $1-\delta$ its real output $\widehat{\mathrm{cost}}(X)$ satisfies
--   $$
--   (1-\varepsilon)\cdot\mathrm{cost}(X)\ \le\ \widehat{\mathrm{cost}}(X)\ \le\ (1+\varepsilon)\cdot\mathrm{cost}(X),\qquad \mathrm{cost}(X)=\sum_{x,y\in X}d(x,y).
--   $$
--
--   This is Stage 4. The cost of every candidate clustering is estimated in sublinear time, so that a nearly best candidate can be selected.
--
--   **Formalization Note** The program runs on `MinSumFPT.Machine` with $k=0$ in the input. The failure event has outer measure at most $\delta$ under the tape law. $\mathrm{cost}(X)$ counts ordered pairs.
--
--   Differences from the source:
--   - generalization: an n point metric space (X, d) → every pseudometric d; reason: Theorem 1's proof applies Theorem 8 to clusters of a semi-metric input; every metric is a pseudometric
--   - reading: O(ε⁻²·n·log(1/δ)) operations → C·ε⁻²·n·log₂(2 + 1/δ) steps on every tape; reason: one constant; log read as log₂(2 + x) ≥ 1 so the bound cannot vanish as δ → 1; worst-case reading
--   - encoding: arithmetic operations, d(x,y) a single operation → steps of MinSumFPT.Machine, every instruction one unit, d read only through dist; reason: the page names no machine; no floor, log, exp or sqrt, so the bound is at least as strong
--   - encoding: the estimate output with probability ≥ 1 − δ → the halted real output; failure set of outer measure ≤ δ under the tape law; reason: outer measure needs no measurability side condition
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 8, p.11

import Mathlib
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumFPT_Machine

namespace MinSumFPT

/-- Theorem 8 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 8, p.11): there is a randomized algorithm that, given an `n`-point
metric space `(X, d)`, a failure probability `δ ∈ (0, 1)` and `ε ∈ (0, 1)`, uses
`O(ε⁻² ⋅ n ⋅ log(1/δ))` operations and outputs an estimate of `cost(X) = ∑_{x,y∈X} d(x, y)` that
lies in `[(1 − ε) ⋅ cost(X), (1 + ε) ⋅ cost(X)]` with probability at least `1 − δ`.

**Formalization Note.** One program of `MinSumFPT.Machine` (inputs `n, ε, δ`; `imem 1 = 0`); on
every tape it halts within `C ⋅ ε⁻² ⋅ n ⋅ log₂(2 + 1/δ)` steps (`log(1/δ)` read as
`log₂(2 + 1/δ)`), and the tapes whose real output lies outside the interval have outer measure at
most `δ`. `cost(X)` counts ordered pairs (`MinSumClust.cost d univ`). `d` is a pseudometric. -/
theorem theorem_8 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℝ,
      ∀ (n : ℕ) (ε δ : ℝ) (d : Fin n → Fin n → ℝ), 1 ≤ n → 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        MinSumClust.IsPseudometric d →
        (∀ ω : ℕ → ℝ, ∃ t, (run P n 0 ε δ d ω t).halted = true ∧
          ((run P n 0 ε δ d ω t).work : ℝ) ≤ C * ε⁻¹ ^ 2 * n * Real.logb 2 (2 + 1 / δ)) ∧
        tapeLaw {ω | ∃ t, (run P n 0 ε δ d ω t).halted = true ∧
            ¬ ((1 - ε) * MinSumClust.cost d Finset.univ ≤ (run P n 0 ε δ d ω t).output ∧
              (run P n 0 ε δ d ω t).output ≤ (1 + ε) * MinSumClust.cost d Finset.univ)} ≤
          ENNReal.ofReal δ := by sorry

end MinSumFPT
