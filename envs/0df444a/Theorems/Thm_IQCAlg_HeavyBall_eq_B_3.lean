-- Prove2me | Theorems.Thm_IQCAlg_HeavyBall_eq_B_3
-- name    : IQCAlg.HeavyBall.eq_B_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:13.942601+00:00
-- url     : https://prove2.me/theorems/fc4a49ae-6a20-4e1f-9edf-ca071f57ab7e
-- title:
--   (B.1)–(B.3), pp. 39–40 — α = 1/9, β = 4/9, and (p, q, r) is the unique solution of the linear system and a 3-cycle of (B.1)
-- statement:
--   For $L=25$ and $m=1$ (so $\kappa=25$), the Heavy-ball parameters of Proposition 1 are
--   $$\alpha=\frac{4}{(\sqrt{25}+\sqrt1)^2}=\frac19,\qquad \beta=\Bigl(\frac{\sqrt{25}-1}{\sqrt{25}+1}\Bigr)^2=\frac49,$$
--   so the update $x_{k+1}=x_k-\alpha\nabla f(x_k)+\beta(x_k-x_{k-1})$ is (B.1): $x_{k+1}=\tfrac{13}9x_k-\tfrac49x_{k-1}-\tfrac19\nabla f(x_k)$.
--
--   Let $p=792/1225$, $q=-2208/1225$, $r=2592/1225$. Then:
--   1. $p<1$, $q<1$ and $r>2$;
--   2. $(p,q,r)$ solves
--   $$\begin{bmatrix}4&12&9\\9&4&12\\12&9&4\end{bmatrix}\begin{bmatrix}p\\q\\r\end{bmatrix}=\begin{bmatrix}0\\24\\0\end{bmatrix},$$
--   and every real solution $(a,b,c)$ of this system equals $(p,q,r)$;
--   3. the period-3 sequence $x^\star=(p,q,r,p,q,r,\dots)$ satisfies (B.1) with $\nabla f$ from (4.11) for every $k$, i.e. the trajectory (B.2) with values (B.3) is a fixed point of (B.1).
--
--   This identifies the limit cycle that the Heavy-ball method approaches in the counterexample.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, pp. 39–40, (B.1), (B.2), the linear system, (B.3) and the sentence after it; p. 6, Proposition 1, last row

import Mathlib
import Definitions.Def_IQCAlg_HeavyBall_Setting

namespace IQCAlg.HeavyBall

/-- (B.1)–(B.3), pp. 39–40: Proposition 1's Heavy-ball tuning at `L = 25`, `m = 1` is
`α = 1/9`, `β = 4/9` (so the update is (B.1)); `p < 1`, `q < 1`, `r > 2`; `(p, q, r)` of (B.3)
solves the linear system of p. 39 and is its unique solution; and the period-3 sequence
`p, q, r, p, …` satisfies (B.1). -/
theorem eq_B_3 :
    hbAlpha 25 1 = 1 / 9 ∧ hbBeta 25 1 = 4 / 9 ∧
    pC < 1 ∧ qC < 1 ∧ 2 < rC ∧
    (4 * pC + 12 * qC + 9 * rC = 0 ∧ 9 * pC + 4 * qC + 12 * rC = 24 ∧
      12 * pC + 9 * qC + 4 * rC = 0) ∧
    (∀ a b c : ℝ, 4 * a + 12 * b + 9 * c = 0 → 9 * a + 4 * b + 12 * c = 24 →
      12 * a + 9 * b + 4 * c = 0 → a = pC ∧ b = qC ∧ c = rC) ∧
    IsB1Traj cyc := by sorry

end IQCAlg.HeavyBall
