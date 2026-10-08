-- Prove2me | Theorems.Thm_MulticutLShaped_Bound_feas_cut_valid
-- name    : MulticutLShaped.Bound.feas_cut_valid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T08:15:29.043243+00:00
-- url     : https://prove2.me/theorems/c7e147b0-aa33-4a1a-8117-e6df5a1f8be2
-- title:
--   Section 2 — the feasibility cuts (5) determine $K_2=\{x \mid \Omega(x)<+\infty\}$
-- statement:
--   Let all scenario probabilities be positive, $p_k>0$. For a scenario $k$ and a basis of the Step 2 feasibility LP
--   $$\min\ e v^+ + e v^-\quad\text{s.t.}\quad Wy+Iv^+-Iv^-=h_k-T_kx',\ \ y,v^+,v^-\ge 0$$
--   that is simplex-optimal at some first-stage point $x'$, with simplex multiplier $\sigma$, let $(D,d)=(\sigma T_k,\sigma h_k)$ be the feasibility cut of type (5) it generates. Then a point $x$ lies in the second-stage feasibility set
--   $$K_2=\{x \mid \Omega(x)<+\infty\},\qquad \Omega(x)=\sum_{k=1}^K p_k Q_k(x),$$
--   if and only if it satisfies every such cut:
--   $$x\in K_2 \iff D x\ \ge\ d\ \text{ for every feasibility cut }(D,d).$$
--
--   This is the statement that the feasibility cuts (5) determine $\{x\mid \Omega(x)<+\infty\}$: no cut removes a point of $K_2$, and every point outside $K_2$ violates the cut generated at that point.
--
--   **Formalization Note** $Q_k(x)$ is extended-real valued, $+\infty$ when Problem $k$ is infeasible. The set $K_2$ is that of the published `StochasticProg_Recourse_Instance`; positive probabilities make it the paper's intersection over all realizations. "Simplex-optimal" means an invertible basic submatrix of $[W\mid I\mid -I]$, a nonnegative basic solution, and nonnegative reduced costs ($\sigma W\le 0$, $-1\le\sigma_i\le 1$).
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 385, Section 2 (feasibility cuts (5)), with Step 2 on p. 386

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases
import Definitions.Def_MulticutLShaped_Bound_Cuts

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix

theorem feas_cut_valid {n1 n2 m1 m2 K : ℕ} (inst : Instance n1 n2 m1 m2 K)
    (hp : ∀ k, 0 < inst.p k) (x : Fin n1 → ℝ) :
    x ∈ K2 inst ↔ ∀ (k : Fin K) (b : FeasBasis n2 m2) (x' : Fin n1 → ℝ),
      IsFeasSimplexOptimal inst k b x' →
        (feasCutCoeffs inst k b).2 ≤ (feasCutCoeffs inst k b).1 ⬝ᵥ x := by sorry

end MulticutLShaped.Bound
