-- Prove2me | Theorems.Thm_GaussDiffSVP_proposition_9_3
-- name    : GaussDiffSVP.proposition_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:59:39.95017+00:00
-- url     : https://prove2.me/theorems/009cdfdb-0ec9-4f00-8a2e-f167324ea077
-- title:
--   Proposition 9.3 — terminal work rate $K_{\mathrm{term}}(E)$ and $\inf_{E>2/e}K_{\mathrm{term}} = -\tfrac12\log_2(1-2^{2\kappa-2})$
-- statement:
--   Fix $0<\kappa<1/2$ and $c = 2^{2\kappa-1}/e$. Under the balance (97) with $\kappa_{\mathrm{pack}} = \kappa$,
--   $$u = 1-\frac c{2a},\qquad L = \frac{P(u)+\kappa}2,\qquad P(\tau) = L,$$
--   and $E = 4a-c>2/e$, the terminal work rate $K_{\mathrm{term}}(E) = K_\tau(u)$ is
--   $$K_{\mathrm{term}}(E) = -\frac12\log_2\Big(2^{1-\kappa}\sqrt{c/E}-c/E\Big),$$
--   and its infimum on this curve is
--   $$\inf_{E>2/e}K_{\mathrm{term}}(E) = -\frac12\log_2(1-2^{2\kappa-2}).$$
--   At $\kappa = 0.401$ the infimum is $0.41296\ldots$, the source of the time exponent $0.4130$.
--
--   Differences from the source:
--   - encoding: $\tau$ with $P(\tau) = L$; $K_{\mathrm{term}}$ as a function of $E$ → every $\tau\in(0,1)$ with $P(\tau) = L$ (it is unique); $E = 4a-c$ parametrized by $a$; reason: same curve
--   - encoding: the infimum → `IsGLB` of the set of values $K_\tau(u)$ over the curve; reason: lower bound and approximation; not attained
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Proposition 9.3, p.44 (balance (97), p.43)

import Mathlib
import Definitions.Def_GaussDiffSVP_rateP
import Definitions.Def_GaussDiffSVP_capRate

namespace GaussDiffSVP

/-- Proposition 9.3 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.44). Fix `0 < κ < 1/2` and `c = 2^{2κ−1}/e`. Under the balance (97)
with `κ_pack = κ` — `u = 1 − c/(2a)`, `L = (P(u) + κ)/2`, `τ` with `P(τ) = L` — and `E = 4a − c > 2/e`,
the terminal work rate `K_term(E) = K_τ(u)` is
`K_term(E) = −½ log₂(2^{1−κ}√(c/E) − c/E)` (98), and its infimum on this curve is
`inf_{E > 2/e} K_term(E) = −½ log₂(1 − 2^{2κ−2})` (99).

**Formalization Note.** `P` and `K_τ` are `rateP` and `capRate`; `τ` ranges over `(0, 1)` with
`P(τ) = L` (it is unique). The infimum is stated as `IsGLB` of the set of values of `K_τ(u)` over
the curve `E > 2/e` (lower bound and approximation; it is not attained). -/
theorem proposition_9_3 (κ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ < 1 / 2) :
    (∀ a : ℝ, 2 / Real.exp 1 < 4 * a - (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1 →
      ∀ τ : ℝ, 0 < τ → τ < 1 →
        rateP τ = (rateP (1 - (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1 / (2 * a)) + κ) / 2 →
        capRate τ (1 - (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1 / (2 * a)) =
          -(1 / 2) * Real.logb 2
            ((2 : ℝ) ^ (1 - κ) * Real.sqrt ((2 : ℝ) ^ (2 * κ - 1) / Real.exp 1 /
                (4 * a - (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1)) -
              (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1 /
                (4 * a - (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1))) ∧
    IsGLB {K : ℝ | ∃ a : ℝ, 2 / Real.exp 1 < 4 * a - (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1 ∧
        ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
          rateP τ = (rateP (1 - (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1 / (2 * a)) + κ) / 2 ∧
          K = capRate τ (1 - (2 : ℝ) ^ (2 * κ - 1) / Real.exp 1 / (2 * a))}
      (-(1 / 2) * Real.logb 2 (1 - (2 : ℝ) ^ (2 * κ - 2))) := by sorry

end GaussDiffSVP
