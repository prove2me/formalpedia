-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_fact_20
-- name    : MatrixSenseRank.Testing.fact_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:46:57.442709+00:00
-- url     : https://prove2.me/theorems/104e05ca-0c3b-471f-9e84-a6020104e232
-- title:
--   Fact 20 — cumulants (corrected: local Taylor radius)
-- statement:
--   For a real probability law $\mu$, write $m_j(\mu)$ for its raw moments and $\kappa_j(\mu)$ for its algebraic cumulants. Suppose its MGF $M_\mu(t)$ is finite for all $|t|<r$, with $r>0$. Every moment exists and there is $0<\rho\le r$ such that
--   $$\log M_\mu(t)=\sum_{j=1}^{\infty}\kappa_j(\mu)\frac{t^j}{j!}\qquad(|t|<\rho).$$
--   All four properties are retained:
--
--   1. For independent laws $\mu,\nu$, each with a positive MGF neighborhood, $\kappa_j(\mu*\nu)=\kappa_j(\mu)+\kappa_j(\nu)$ for every $j\ge1$.
--   2. For every real $c$, $\kappa_j(cX)=c^j\kappa_j(X)$ for every $j\ge1$.
--   3. For every $\ell$, two such laws have equal first $\ell$ moments if and only if they have equal first $\ell$ cumulants.
--   4. If $Z=GH$ for independent standard normals, then $\kappa_{2j}(Z)=(2j-1)!$ for every $j\ge1$, and every odd cumulant vanishes.
--
--   This proves analytic compatibility of the finite-moment cumulant definition and supplies the product-normal cumulants used in §6. The analytic hypotheses remain confined to this fact, not the arbitrary noise in the testing theorems.
--
--   Differences from the source:
--   - correction: the cumulant Taylor expansion holds throughout every interval |t|<r of MGF finiteness → there exists 0<ρ≤r on which that Taylor expansion converges; reason: for X uniform on {-1,1} and r=2, the MGF cosh(t) is finite everywhere, but log cosh(t) has Taylor radius π/2 and its series diverges at 7/4<2; this is the minimal local-radius correction and changes none of clauses (i)–(iv)
--   - encoding: random variables, analytic cumulants and determination by first ℓ moments → probability laws, moment-cumulant polynomials, a convergent HasSum identity and equality of the first ℓ moments iff equality of the first ℓ cumulants; reason: pushforwards describe independent addition and scaling, and the local expansion proves compatibility of the analytic and algebraic conventions; the positive MGF neighborhoods make all moments integrable
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, STOC 2027 submission #380 (October 2026), §7.1.2, Fact 20, printed p. 32 / PDF p. 33; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf; PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b.

import Mathlib
import Definitions.Def_MatrixSenseRank_Testing_Moments

set_option autoImplicit false
open MeasureTheory

namespace MatrixSenseRank.Testing

/-- Fact 20 (corrected: local Taylor radius), printed p.32 / PDF p.33.
For Rademacher X and r=2 the printed expansion on the whole interval is false:
log cosh has Taylor radius pi/2, so its series diverges at 7/4 < 2.
All four clauses are retained, and cumulants are finite-moment polynomials. -/
theorem fact_20 :
    (∀ (μ : Measure ℝ), IsProbabilityMeasure μ → ∀ r : ℝ, MGFNeighborhood μ r →
      (∀ q : ℕ, FiniteMoments μ q) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∀ t : ℝ, |t| < ρ →
        HasSum (fun j : ℕ => cumulant μ (j + 1) * t ^ (j + 1) /
          ((j + 1).factorial : ℝ)) (Real.log (mgfValue μ t))) ∧
    (∀ (μ ν : Measure ℝ), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∃ r : ℝ, MGFNeighborhood μ r) → (∃ r : ℝ, MGFNeighborhood ν r) →
      ∀ j : ℕ, 1 ≤ j → cumulant (independentSum μ ν) j = cumulant μ j + cumulant ν j) ∧
    (∀ (μ : Measure ℝ), IsProbabilityMeasure μ → (∃ r : ℝ, MGFNeighborhood μ r) →
      ∀ (c : ℝ) (j : ℕ), 1 ≤ j → cumulant (scaledLaw c μ) j = c ^ j * cumulant μ j) ∧
    (∀ (μ ν : Measure ℝ), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
      (∃ r : ℝ, MGFNeighborhood μ r) → (∃ r : ℝ, MGFNeighborhood ν r) →
      ∀ ℓ : ℕ,
        (∀ j : ℕ, 1 ≤ j → j ≤ ℓ → rawMoment μ j = rawMoment ν j) ↔
        (∀ j : ℕ, 1 ≤ j → j ≤ ℓ → cumulant μ j = cumulant ν j)) ∧
    (∀ j : ℕ, 1 ≤ j → cumulant productNormal (2 * j) = ((2 * j - 1).factorial : ℝ)) ∧
    (∀ j : ℕ, cumulant productNormal (2 * j + 1) = 0) := by sorry

end MatrixSenseRank.Testing
