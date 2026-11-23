-- Prove2me | Theorems.Thm_GrothendieckLB_Supplement_theorem_5_1
-- name    : GrothendieckLB.Supplement.theorem_5_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T14:44:00.93707+00:00
-- url     : https://prove2.me/theorems/c7185baf-60a8-469a-b326-23f2af45941d
-- title:
--   Theorem 5.1: coefficient formula $b_m=\frac\pi2\sum_{a+b\le m}(-1)^bA_{a,b}^2[t^{m-b}]\rho(t)^a$
-- statement:
--   Let $H(t)=\sum_{m\ge1}b_mt^m$ be the correlation function of the cubic–quintic scheme, $\rho$ its correlation map (11) and $A_{a,b}$ the Hermite coefficients (14). Then:
--
--   1. for every $t\in(-1,1)$,
--   $$
--   H(t)=\frac\pi2\sum_{a,b\ge0}A_{a,b}^2\,\rho(t)^a(-t)^b ;\tag{15}
--   $$
--   2. for every $m\ge1$,
--   $$
--   b_m=\frac\pi2\sum_{\substack{a,b\ge0\\ a+b\le m}}(-1)^bA_{a,b}^2\,[t^{m-b}]\rho(t)^a ;\tag{16}
--   $$
--   3. $b_m=0$ whenever $m$ is even.
--
--   This reduces every Taylor coefficient of $H$ to finitely many one-dimensional Gaussian integrals and polynomial coefficients, which is how the coefficient head is certified.
--
--   **Formalization Note** The double series (15) is stated as an unconditionally (absolutely) convergent sum over $\mathbb N\times\mathbb N$; $b_m$ is the Taylor coefficient $H^{(m)}(0)/m!$; $[t^j]\rho(t)^a$ is a polynomial coefficient.
--
--   Differences from the source:
--   - generalization: the cubic–quintic scheme with the parameters (10) → all real parameters (η, s₃, s₅); reason: the proof uses only g(w, x) = f(w, −x), oddness of f and |ρ(t)| ≤ |t| < 1, which hold for every parameter choice; specializing to (10) gives the page's statement
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 5.1, (15), (16), p.25

import Mathlib
import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_Supplement_cqCorr
import Definitions.Def_GrothendieckLB_Supplement_cqA

namespace GrothendieckLB

namespace Supplement

/-- Theorem 5.1, coefficient formula (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Theorem 5.1, (15), (16), p.25): for the cubic–quintic
scheme with correlation function `H(t) = ∑_{m ≥ 1} b_m t^m` and Hermite coefficients `A_{a,b}` (14),
for every `t ∈ (−1, 1)`, `H(t) = (π/2) ∑_{a,b ≥ 0} A²_{a,b} ρ(t)^a (−t)^b` (15). Consequently, for
every `m ≥ 1`, `b_m = (π/2) ∑_{a + b ≤ m} (−1)^b A²_{a,b} [t^{m−b}] ρ(t)^a` (16). In particular,
`b_m = 0` whenever `m` is even.

**Formalization Note** Stated for all real parameters `(η, s₃, s₅)`, which includes (10).
(15) is an unconditionally (absolutely) convergent double series over `ℕ × ℕ` (`HasSum`).
`b_m = taylorCoeff m H`, the sum over `a + b ≤ m` is the finite sum over `a ≤ m`, `b ≤ m − a`,
and `[t^j] ρ(t)^a` is the polynomial coefficient `((cqRhoPoly s₃ s₅) ^ a).coeff j`. -/
theorem theorem_5_1 (η s₃ s₅ : ℝ) :
    (∀ t : ℝ, |t| < 1 →
      HasSum (fun p : ℕ × ℕ => Real.pi / 2 * (cqA η s₃ s₅ p.1 p.2) ^ 2 *
          ((cqRhoPoly s₃ s₅).eval t) ^ p.1 * (-t) ^ p.2) (cqCorr η s₃ s₅ t)) ∧
    (∀ m : ℕ, 1 ≤ m → taylorCoeff m (cqCorr η s₃ s₅) =
      Real.pi / 2 * ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m + 1 - a),
        (-1 : ℝ) ^ b * (cqA η s₃ s₅ a b) ^ 2 * ((cqRhoPoly s₃ s₅) ^ a).coeff (m - b)) ∧
    (∀ m : ℕ, 1 ≤ m → Even m → taylorCoeff m (cqCorr η s₃ s₅) = 0) := by sorry

end Supplement

end GrothendieckLB
