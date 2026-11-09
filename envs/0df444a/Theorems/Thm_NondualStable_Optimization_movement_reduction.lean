-- Prove2me | Theorems.Thm_NondualStable_Optimization_movement_reduction
-- name    : NondualStable.Optimization.movement_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:17.128006+00:00
-- url     : https://prove2.me/theorems/59ebf146-722a-4541-9ff5-ef30161c76df
-- title:
--   Proposition 5 — Movement-to-optimization reduction
-- statement:
--   Let $1\le p\le q\le\infty$ and $0<\rho\le1$. Fix a positive movement constant $A$ and a nonnegative integer logarithmic degree $k$. Suppose an online selector $C$ is feasible for every nested compact convex request prefix in $R B_p^d$ and, for every horizon $H\ge1$, has movement at most
--   $$A R H^{1-\rho}\bigl[1+\log(2d+2)+\log(2+H)\bigr]^k.$$
--   There exist uniform $B>0$ and a finite degree $j$ such that, for every globally convex $G$-Lipschitz objective, positive $G,R,\varepsilon$, valid history-dependent first-order oracle and certified model solver, Algorithm 1 terminates with a feasible best queried point and certificate of width at most $\varepsilon$, using at most
--   $$B\bigl[1+(GR/\varepsilon)^{1/\rho}\bigr]\bigl[1+\log(2d+2)+\log(2+GR/\varepsilon)\bigr]^j$$
--   first-order calls. Every query is feasible. Initialization, the first center of each phase and terminal queries all contribute to this count. This theorem concerns oracle complexity; the numerical solver is not asserted to have unit real-arithmetic cost.
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: uniform O or Õ bounds → positive constants and finite natural logarithmic or polynomial degrees quantified before every instance parameter; reason: this expands the uniform asymptotics in Section 2 and the quantitative bounds in Appendices E–G
--   - encoding: Algorithm 1 with a selector and model-minimum certificates → iteration of the operational bundle transition with arbitrary certified model solvers and online request-prefix selectors; reason: the solver contract is exactly line 6 and all first-order calls are counted by actual history entries
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed pp. 7–8/PDF pp. 8–9, Proposition 5 and (5)–(6); proof printed p. 19/PDF p. 20

import Definitions.Def_NondualStable_Optimization_Bundle
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Proposition 5, printed pp.7-8 / PDF pp.8-9. Uniform movement
constants precede all instance data. Every oracle call, including initialization,
first centers and terminal calls, appears in the history length. -/
theorem movement_reduction (p q : ℝ≥0∞) (hp : 1 ≤ p) (hpq : p ≤ q)
    (ρ A : ℝ) (hρ : 0 < ρ ∧ ρ ≤ 1) (hA : 0 < A) (k : ℕ) :
    ∃ B : ℝ, ∃ j : ℕ, 0 < B ∧
      ∀ d : ℕ, 0 < d → ∀ G R ε : ℝ, 0 < G → 0 < R → 0 < ε →
      ∀ f : Vec d → ℝ, Objective q G f → ∀ O : Oracle d, ValidOracle p q G R f O →
      ∀ C : List (Set (Vec d)) → Vec d, StableSelector p q R ρ A k C →
      ∀ S : ModelSolver d, ValidModelSolver p R S →
      ∃ n : ℕ,
        let s := bundleRun G R ε O S (fun b => C (phaseBodies p R b)) n
        s.done = true ∧ CertifiedOutput p R ε f s ∧
        (s.history.length : ℝ) ≤ oracleBudget B j ρ d G R ε ∧
        ∀ o ∈ s.history, o.point ∈ ball p R := by sorry

end NondualStable.Optimization
