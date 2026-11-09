-- Prove2me | Theorems.Thm_NondualStable_Optimization_polynomial_implementation
-- name    : NondualStable.Optimization.polynomial_implementation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:30.81332+00:00
-- url     : https://prove2.me/theorems/acb6ff41-947f-44aa-add2-96fedb7ad220
-- title:
--   Theorem 12 — Polynomial-time implementation
-- statement:
--   Fix $1\le p\le\min\{q,2\}$, $q\in(1,\infty]$, and $\rho=1/p-(1/q-1/2)_+$. There exist positive constants $B,C$, finite natural degrees $j,k$, and one finite instruction program, all chosen before the instance data. For every $d\ge1$, positive $G,R,\varepsilon$ and $0<\delta<1$, this program implements Algorithm 1 and uses at most
--   $$B\bigl[1+(GR/\varepsilon)^{1/\rho}\bigr]\bigl[1+\log(2d+2)+\log(2+GR/\varepsilon)\bigr]^j$$
--   first-order calls and at most $C[d+2+GR/\varepsilon+\log(1/\delta)]^k$ additional real operations. The query budget is chosen before the confidence parameter. These bounds and query/output feasibility hold on every realization of the randomness and for every valid adaptive oracle.
--
--   For every globally convex $G$-Lipschitz objective the constrained minimum is attained, and, with probability at least $1-\delta$, the returned best point and lower value satisfy
--   $$\ell\le\min_{x\in R B_p^d}f(x)\le f(x_{\rm best})\le\ell+\varepsilon.$$
--   The code has no free call to the objective, an exact expectation, an argmin or an ellipsoid solve. The algorithmic conclusion includes an operational bundle trace and permits the source's safe early returns.
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: uniform O or Õ bounds → positive constants and finite natural logarithmic or polynomial degrees quantified before every instance parameter; reason: this expands the uniform asymptotics in Section 2 and the quantitative bounds in Appendices E–G
--   - encoding: randomized procedures and adaptive oracle choices → independent standard Gaussian product tapes and jointly measurable causal oracle or request maps; reason: probabilities refer to measurable random procedures; arbitrary measurable history-dependent bounded subgradient choices remain allowed
--   - encoding: polynomial time in the real-arithmetic model → a finite instruction program with registers, branches, rational powers, logarithms, Gaussian draws and charged oracle interaction; reason: every numerical solve must consist of permitted instructions; the objective, an exact center and a minimizer are unavailable as free instructions
--   - encoding: minimum and certificate in the displayed conclusion → attainment is a conclusion and the lower bound quantifies against every feasible point; reason: equivalent to the displayed minimum certificate and avoids an unguarded real infimum
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 12/PDF p. 13, Theorem 12; proof printed pp. 25–28/PDF pp. 26–29, (36),(38)–(40)

import Definitions.Def_NondualStable_Optimization_RealMachine
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Theorem 12, printed p.12 / PDF p.13. The query bound is chosen
before delta. Programs and polynomial degrees are chosen before instance data;
all arithmetic, including numerical solves, must execute in the instruction model.
The external bound Q is not supplied to the program as advice (T input is zero). -/
theorem polynomial_implementation (p q : ℝ≥0∞) (hpq : admissible p q) :
    ∃ B C : ℝ, ∃ j k : ℕ, ∃ P : Program, 0 < B ∧ 0 < C ∧
      ∀ d : ℕ, 0 < d → ∀ G R ε : ℝ, 0 < G → 0 < R → 0 < ε →
      ∃ Q : ℕ, (Q : ℝ) ≤ oracleBudget B j (rate p q) d G R ε ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∃ fuel : ℕ, (fuel : ℝ) ≤ operationBudget C k d (1 + G * R / ε) δ ∧
      ∀ f : Vec d → ℝ, Objective q G f →
      ∀ O : Oracle d, ValidOracle p q G R f O → OracleMeasurable O →
        (∃ v : ℝ, Minimum (ball p R) f v) ∧
        (∀ ω : Tape,
          let s := execute P 0 G R ε δ O ω fuel
          Safe p R Q s ∧ (s.operations : ℝ) ≤ operationBudget C k d (1 + G * R / ε) δ ∧
          BundleImplementation p G R ε O s) ∧
        MeasurableSet {ω | CertificateAccurate p R ε f (execute P 0 G R ε δ O ω fuel)} ∧
        tapeLaw {ω | CertificateAccurate p R ε f (execute P 0 G R ε δ O ω fuel)} ≥
          ENNReal.ofReal (1 - δ) := by sorry

end NondualStable.Optimization
