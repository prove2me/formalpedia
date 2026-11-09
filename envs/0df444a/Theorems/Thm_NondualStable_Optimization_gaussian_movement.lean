-- Prove2me | Theorems.Thm_NondualStable_Optimization_gaussian_movement
-- name    : NondualStable.Optimization.gaussian_movement
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:54.256282+00:00
-- url     : https://prove2.me/theorems/558874e9-3184-426c-b06b-25de19a7aacc
-- title:
--   Theorem 9 — Mixed-norm Gaussian movement
-- statement:
--   For each $q\in(1,\infty]$, a constant $C_q>0$ exists uniformly over $1\le p\le\min\{q,2\}$, $d\ge1$, $R>0$, and integer horizons $H\ge1$. For every nested sequence of nonempty compact convex subsets of $R B_p^d$, the Gaussian reference center is well-defined and feasible, and
--   $$\sum_{t<H}\|C_{p,q,H}(K^{t+1})-C_{p,q,H}(K^t)\|_q\le C_q R H^{1-\rho}\left[1+\sqrt{L_d}(\log(2H))^{1-1/r}\right],\quad \rho=1/p-(1/q-1/2)_+,\quad r=\min\{q,2\}.$$
--   The horizon remains fixed in every center in the path. Requests need no interior ball. This is absolute movement, including both head and tail components.
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: Õ movement in Theorem 9 → the explicit Cq profile from the final display of its proof, with Cq before p,d,R,H and the requests; reason: preserves the stronger quantitative profile used by the implementation
--   - encoding: center defined by a Gaussian expectation → optimizer existence, uniqueness, measurability, sample integrability and center feasibility are conclusions; reason: prevents an undefined optimizer or a Bochner default from representing the source center
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 10/PDF p. 11, Theorem 9; quantitative final display printed p. 22/PDF p. 23

import Definitions.Def_NondualStable_Optimization_GaussianCenter
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Theorem 9, printed p.10 / PDF p.11; quantitative profile from the
final display on printed p.22 / PDF p.23. C depends only on q. -/
theorem gaussian_movement (q : ℝ≥0∞) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ≥0∞, admissible p q →
      ∀ d H : ℕ, 0 < d → 1 ≤ H → ∀ R : ℝ, 0 < R →
      ∀ K : ℕ → Set (Vec d), Nested p R H K →
        (∀ t ≤ H, CenterWellDefined p q R H (K t)) ∧
        movement q H (fun t => center p q R H (K t)) ≤ movementProfile C p q d R H := by sorry

end NondualStable.Optimization
