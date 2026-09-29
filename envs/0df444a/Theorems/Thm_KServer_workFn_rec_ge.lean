-- Prove2me | Theorems.Thm_KServer_workFn_rec_ge
-- name    : KServer.workFn_rec_ge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:38:15.671331+00:00
-- url     : https://prove2.me/theorems/a4b38558-c5a7-4683-8884-225de82f3e62
-- title:
--   The work-function recurrence, lower half: some server attains the minimum
-- statement:
--   Some server realises the work-function recurrence: for every target configuration $X$ there is an index $i$ with
--   $$w\bigl(C_0;\sigma;X[i\mapsto r]\bigr)+d\bigl(r,X_i\bigr)\;\le\;w(C_0;\sigma\cdot r;X),$$
--   where $X[i\mapsto r]$ is $X$ with server $i$ relocated to the request $r$.
--
--   **Role.** Together with the companion upper bound `KServer.workFn_rec_le`, which gives the reverse inequality for *every* $i$, this is the recurrence
--   $$w_t(X)\;=\;\min_{x\in X}\bigl\{w_{t-1}(X-x+r_t)+d(r_t,x)\bigr\}$$
--   that determines the work function at time $t$ from its values at time $t-1$, and hence computes it by dynamic programming. It is the first of the standard properties of work functions and the engine behind every analysis built on them, including the Work Function Algorithm's $(2k-1)$-competitiveness.
--
--   The content of this direction is that an optimal solution ending at $X$ after serving $r$ can be *read backwards*: at the moment $r$ was served some server stood on it, and that server is the one the recurrence names. The statement is existential rather than an explicit minimum because the witness depends on the solution; since there are finitely many servers the minimum is attained, so the existential form is the sharp one.
--
--   **Formalization Note** In the classical treatment work functions are functions of unordered configurations, where $X-x+r$ is unambiguous. Here configurations are labelled, `Config k M = Fin k → M`, so the natural transcription of $X-x+r$ is `Function.update X i r`, and ranging over servers $i$ replaces the minimum over points $x\in X$. The final repositioning cost between $X[i\mapsto r]$ and $X$ collapses to the single term $d(r,X_i)$ because the two configurations agree off the index $i$.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, property 1 of work functions following equation (4): "If r_t not in X, then w_t(X) = w_t(X - x + r_t) + d(r_t,x) for some x in X", i.e. the lower bound in w_t(X) = min over x in X of (w_{t-1}(X - x + r_t) + d(r_t,x)); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_rec_ge (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    ∃ i : Fin k, workFn C₀ σ (Function.update X i r) + dist r (X i)
      ≤ workFn C₀ (σ ++ [r]) X := by sorry

end KServer
