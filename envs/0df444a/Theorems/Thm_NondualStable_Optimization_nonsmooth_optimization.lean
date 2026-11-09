-- Prove2me | Theorems.Thm_NondualStable_Optimization_nonsmooth_optimization
-- name    : NondualStable.Optimization.nonsmooth_optimization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:44:12.86806+00:00
-- url     : https://prove2.me/theorems/23bdf1ab-a4d0-4feb-8c4c-7e2da0d264e1
-- title:
--   Theorem 3 — Efficient nonsmooth lp/lq optimization
-- statement:
--   Fix real norm parameters $1\le p\le\min\{q,2\}$ with $q\in(1,\infty]$, and put $\rho=1/p-(1/q-1/2)_+$. There are positive constants $B,C$, finite natural degrees $j,k$ and a single finite real-arithmetic oracle program, chosen before all instance data. For every dimension $d\ge1$, integer budget $T\ge2$, $G,R\ge0$, confidence $0<\delta<1$, globally convex $G$-Lipschitz objective in $\ell_q$, and valid adaptive first-order oracle, the program halts with feasible output $\hat x_T\in R B_p^d$ and makes at most $T$ feasible first-order queries on every run. It uses at most $C[d+1+T+\log(1/\delta)]^k$ additional real operations. With probability at least $1-\delta$,
--   $$f(\hat x_T)-\min_{x\in R B_p^d}f(x)\le BGR T^{-\rho}\bigl[1+\log(2d+2)+\log(2+T)\bigr]^j.$$
--   The minimum is attained. The result includes $q=\infty$, $p=q$ where admissible, $p=2$ for $q\ge2$, and every budget $T\ge2$ without a $T\le d$ condition. If $GR=0$, the feasible output is obtained without an oracle query.
--
--   This is the full algorithmic upper bound: the error contains only logarithmic dimension factors, and neither confidence nor numerical computation relaxes the exact query cap.
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: uniform O or Õ bounds → positive constants and finite natural logarithmic or polynomial degrees quantified before every instance parameter; reason: this expands the uniform asymptotics in Section 2 and the quantitative bounds in Appendices E–G
--   - encoding: randomized procedures and adaptive oracle choices → independent standard Gaussian product tapes and jointly measurable causal oracle or request maps; reason: probabilities refer to measurable random procedures; arbitrary measurable history-dependent bounded subgradient choices remain allowed
--   - encoding: polynomial time in the real-arithmetic model → a finite instruction program with registers, branches, rational powers, logarithms, Gaussian draws and charged oracle interaction; reason: every numerical solve must consist of permitted instructions; the objective, an exact center and a minimizer are unavailable as free instructions
--   - encoding: minimum error in (3) → attainment is concluded and error compares against every feasible point; reason: equivalent to comparison with the attained minimum
--   - generalization: the nontrivial positive G,R scaling regime → nonnegative G,R with a zero-query feasible branch when GR=0; reason: a zero-radius ball contains only zero, and a globally zero-Lipschitz objective is constant
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 6/PDF p. 7, Theorem 3, (3); proof printed p. 28/PDF p. 29, Appendix G

import Definitions.Def_NondualStable_Optimization_RealMachine
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Theorem 3 (goal), printed p.6 / PDF p.7. Full first-order and
real-arithmetic guarantee, including q=infinity and every real finite exponent.
Uniform constants and logarithmic/polynomial degrees precede all instances. -/
theorem nonsmooth_optimization (p q : ℝ≥0∞) (hpq : admissible p q) :
    ∃ B C : ℝ, ∃ j k : ℕ, ∃ P : Program, 0 < B ∧ 0 < C ∧
      ∀ d T : ℕ, 0 < d → 2 ≤ T →
      ∀ G R δ : ℝ, 0 ≤ G → 0 ≤ R → 0 < δ → δ < 1 →
      ∃ fuel : ℕ, (fuel : ℝ) ≤ operationBudget C k d T δ ∧
      ∀ f : Vec d → ℝ, Objective q G f →
      ∀ O : Oracle d, ValidOracle p q G R f O → OracleMeasurable O →
        (∃ v : ℝ, Minimum (ball p R) f v) ∧
        (∀ ω : Tape,
          let s := execute P T G R 0 δ O ω fuel
          Safe p R T s ∧ (s.operations : ℝ) ≤ operationBudget C k d T δ ∧
          (G * R = 0 → s.history.length = 0)) ∧
        MeasurableSet {ω | Accurate p R (errorBudget B j (rate p q) d T G R) f
          (execute P T G R 0 δ O ω fuel)} ∧
        tapeLaw {ω | Accurate p R (errorBudget B j (rate p q) d T G R) f
          (execute P T G R 0 δ O ω fuel)} ≥ ENNReal.ofReal (1 - δ) := by sorry

end NondualStable.Optimization
