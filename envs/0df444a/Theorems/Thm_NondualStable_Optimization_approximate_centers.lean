-- Prove2me | Theorems.Thm_NondualStable_Optimization_approximate_centers
-- name    : NondualStable.Optimization.approximate_centers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:30.499196+00:00
-- url     : https://prove2.me/theorems/f9965fcb-d1d0-4eb8-964d-12ba145b317f
-- title:
--   Lemma 6 — Oracle complexity under approximate centers
-- statement:
--   Let $1\le p\le q\le\infty$ and $0<\rho\le1$. Suppose reference centers in every phase obey the uniform movement profile in Proposition 5, and the feasible provided centers satisfy
--   $$\|\hat z^t-z^t\|_q\le\frac{\Gamma}{16G}.$$
--   Algorithm 1 then has the same uniform oracle-complexity bound, a feasible output with a certified $\varepsilon$ gap, and feasible queries throughout. Constants and finite logarithmic degrees depend on the fixed movement profile and norm parameters, never on the instance, oracle or tolerances.
--
--   The statement also retains the proof's exact deterministic charge: if $N$ consecutive actual transitions each have length at least $\Gamma/(2G)$ and the above pointwise approximation holds for all $0\le t\le N$, then
--   $$\frac{3N\Gamma}{8G}\le\sum_{t<N}\|z^{t+1}-z^t\|_q.$$
--   For each actual phase, one reference sequence is fixed before its prefix length is chosen. Its feasibility, approximation error and movement bound are required only on the requests actually queried in that phase; no globally stable selector on other request sequences is assumed. This result permits numerical center approximations without assuming the desired termination rate in a run record.
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: uniform O or Õ bounds → positive constants and finite natural logarithmic or polynomial degrees quantified before every instance parameter; reason: this expands the uniform asymptotics in Section 2 and the quantitative bounds in Appendices E–G
--   - encoding: approximate reference-center sequences within each phase → reference sequences for prefixes of actual queried phases of the operational bundle run, with explicit feasibility, pointwise error and movement contracts; reason: expresses the source phase-local hypothesis without requiring a stable selector on unrelated request sequences
--   - generalization: the lemma states the oracle-complexity conclusion → the conclusion also includes the exact deterministic 3NΓ/(8G) reference-movement inequality; reason: this additional conclusion is proved explicitly in Appendix D, printed p. 20, and retains the entire complexity conclusion
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 8/PDF p. 9, Lemma 6; proof printed p. 20/PDF p. 21

import Definitions.Def_NondualStable_Optimization_Bundle
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Lemma 6, printed p.8 / PDF p.9. The first clause records the
exact 3N*Gamma/(8G) inequality from its proof, printed p.20 / PDF p.21. -/
theorem approximate_centers (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q)
    (ρ A : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1) (hA : 0 < A) (k : ℕ) :
    (∀ (d N : ℕ) (G Γ : ℝ), 0 < G → 0 < Γ →
      ∀ z zh : ℕ → Vec d,
      (∀ t ≤ N, lpNorm q (zh t - z t) ≤ Γ / (16 * G)) →
      (∀ t < N, Γ / (2 * G) ≤ lpNorm q (zh (t + 1) - zh t)) →
      3 * (N : ℝ) * Γ / (8 * G) ≤ movement q N z) ∧
    ∃ B : ℝ, ∃ j : ℕ, 0 < B ∧
      ∀ d : ℕ, 0 < d → ∀ G R ε : ℝ, 0 < G → 0 < R → 0 < ε →
      ∀ f : Vec d → ℝ, Objective q G f → ∀ O : Oracle d, ValidOracle p q G R f O →
      ∀ S : ModelSolver d, ValidModelSolver p R S →
      ∀ P : CenterProvider d,
      ApproximateProvider p q G R ε ρ A k O S P →
      ∃ n : ℕ,
        let s := bundleRun G R ε O S P n
        s.done = true ∧ CertifiedOutput p R ε f s ∧
        (s.history.length : ℝ) ≤ oracleBudget B j ρ d G R ε ∧
        ∀ o ∈ s.history, o.point ∈ ball p R := by sorry

end NondualStable.Optimization
