-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_heavy_ball_limit_cycle
-- name    : IQCAlg.HeavyBall.heavy_ball_limit_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:13.124813+00:00
-- url     : https://prove2.me/theorems/c274f09f-d639-4c36-9a7f-ee161a4654bb
-- title:
--   Appendix B, pp. 39–40 — Heavy-ball tuned for quadratics, from x₀ = 3.3 on (4.11), converges to the 3-cycle (792, −2208, 2592)/1225
-- statement:
--   Let $\nabla f$ be the piecewise-linear gradient (4.11), so that $f\in S(1,25)$ and $f$ has its unique minimizer at $0$. Run the Heavy-ball method
--   $$x_{k+1}=x_k-\alpha\nabla f(x_k)+\beta(x_k-x_{k-1})$$
--   with the parameters that Proposition 1 shows to be optimal on quadratics for $L=25$, $m=1$,
--   $$\alpha=\frac4{(\sqrt{25}+\sqrt1)^2},\qquad \beta=\Bigl(\frac{\sqrt{25}-1}{\sqrt{25}+1}\Bigr)^2,$$
--   from $x_0=3.3$ with $x_{-1}=x_0$. Then, as $n\to\infty$,
--   $$x_{3n}\to\frac{792}{1225},\qquad x_{3n+1}\to-\frac{2208}{1225},\qquad x_{3n+2}\to\frac{2592}{1225}.$$
--
--   The iterates converge to a cycle of period 3, not to the minimizer $0$ of $f$: the Heavy-ball method optimized for quadratics does not converge for general $f\in S(m,L)$, even though every quadratic in this class is handled at the optimal rate. This is the counterexample of Section 4.6, proved in Appendix B.
--
--   **Formalization Note** The sequence is indexed from $x_0$, so the page's initialization $x_{-1}=x_0$ appears as $x_1=x_0-\alpha\nabla f(x_0)$. The parameters are written as in Proposition 1 rather than as $1/9$ and $4/9$.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, pp. 39–40, Appendix B, (B.1)–(B.3) and "Therefore, the limit cycle is attractive"; p. 23, Section 4.6

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace IQCAlg.HeavyBall

/-- Appendix B, pp. 39–40: the Heavy-ball method with Proposition 1's tuning for
`L = 25`, `m = 1`, run on the gradient (4.11) from `x_0 = 3.3` (with `x_{−1} = x_0`), has
`x_{3n} → 792/1225`, `x_{3n+1} → −2208/1225`, `x_{3n+2} → 2592/1225`: the limit cycle (B.3)
is attractive. -/
theorem heavy_ball_limit_cycle :
    Filter.Tendsto (fun n : ℕ => hbRun gradF (hbAlpha 25 1) (hbBeta 25 1) (33 / 10) (3 * n))
        Filter.atTop (nhds (792 / 1225)) ∧
    Filter.Tendsto (fun n : ℕ => hbRun gradF (hbAlpha 25 1) (hbBeta 25 1) (33 / 10) (3 * n + 1))
        Filter.atTop (nhds (-2208 / 1225)) ∧
    Filter.Tendsto (fun n : ℕ => hbRun gradF (hbAlpha 25 1) (hbBeta 25 1) (33 / 10) (3 * n + 2))
        Filter.atTop (nhds (2592 / 1225)) := by sorry

end IQCAlg.HeavyBall
