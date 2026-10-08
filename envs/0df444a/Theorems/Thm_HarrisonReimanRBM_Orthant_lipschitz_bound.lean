-- Prove2me | Theorems.Thm_HarrisonReimanRBM_Orthant_lipschitz_bound
-- name    : HarrisonReimanRBM.Orthant.lipschitz_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:22:19.451298+00:00
-- url     : https://prove2.me/theorems/4a7940f3-bd5c-43a6-abae-b859c81cf111
-- title:
--   Lipschitz bound: $\|\psi(x)-\psi(x')\|\le\|x-x'\|/(1-\alpha)$ on $[0,T]$
-- statement:
--   Let $K\ge1$ and let $Q$ be a nonnegative $K\times K$ matrix with zeros on the diagonal and maximal column sum $\alpha=\max_j\sum_i q_{ij}<1$. Let $x,x'\in C_S$, and let $(y,z)$ and $(y',z')$ satisfy (5)–(8) for $Q$ with $x$ and $x'$ respectively, i.e. $y=\psi(x)$, $y'=\psi(x')$. Then for every $T>0$,
--   $$\|y-y'\|\le\frac{\|x-x'\|}{1-\alpha},$$
--   where $\|w\|=\max_{1\le j\le K}\sup_{0\le t\le T}|w_j(t)|$.
--
--   This gives the continuity (10) of $\psi$ in the topology of uniform convergence on compact intervals, and with (15) that of $\phi$.
--
--   **Formalization Note** The paper derives the bound from the one-step inequality $\|y^{n+1}(x)-y^{n+1}(x')\|\le\|x-x'\|+\alpha\|y^n(x)-y^n(x')\|$ for the Picard iterates; the final bound is stated here for solutions of (5)–(8), which avoids defining $\psi$ by choice. As in the contraction milestone, $\alpha$ is the maximal column sum (the printed "row sum" is the column sum under the row-vector convention). The paper takes $x,x'\in C_S[0,T]$; here they are in $C_S$ on $[0,\infty)$, and by (9) only their restrictions to $[0,T]$ matter.
-- source:
--   Harrison & Reiman, Reflected Brownian Motion on an Orthant, Ann. Probab. 9(2) (1981), p. 305, proof of Theorem 1 (continuity property (10))

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_HarrisonReimanRBM_Orthant_Basic

namespace HarrisonReimanRBM.Orthant

open Reiman84.QueueLength

/-- Proof of Theorem 1, p. 305: if `Q ≥ 0` has zero diagonal and maximal column sum
`α < 1`, then for `x, x' ∈ C_S` with `y = ψ(x)`, `y' = ψ(x')`,
`‖y − y'‖ ≤ ‖x − x'‖ / (1 − α)` in the norm `max_j sup_{0 ≤ t ≤ T} |·_j(t)|`. -/
theorem lipschitz_bound {K : ℕ} (hK : 0 < K) (Q : Matrix (Fin K) (Fin K) ℝ)
    (hQ0 : ∀ i j, 0 ≤ Q i j) (hQd : ∀ j, Q j j = 0) (α : ℝ) (hα : maxColSum Q = α)
    (hα1 : α < 1) (x y z x' y' z' : ℝ → Fin K → ℝ) (h : IsReflectionPair Q x y z)
    (h' : IsReflectionPair Q x' y' z') (T : ℝ) (hT : 0 < T) :
    supNormOn T (y - y') ≤ supNormOn T (x - x') / (1 - α) := by sorry

end HarrisonReimanRBM.Orthant
