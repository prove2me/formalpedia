-- Prove2me | Theorems.Thm_KServer_workFn_nil
-- name    : KServer.workFn_nil
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:43:25.741833+00:00
-- url     : https://prove2.me/theorems/2a8ef9f9-36aa-4f6e-97c0-0054ba2076c6
-- title:
--   Bootstrap value of the work function
-- statement:
--   Before any request has arrived, the work function is just the distance from the initial configuration:
--   $$w(C_0;\varnothing;X)\;=\;\mathrm{moveCost}(C_0,X).$$
--
--   **Role.** This is the bootstrapping value $w_0(X)=d(C_0,X)$ from which the dynamic programming that computes work functions starts; together with the recurrence in the number of requests it determines $w_t$ for every $t$. It is also the base case of every induction over request sequences that carries a work function, and the reason the initial value of a potential built from work functions is a constant depending only on $C_0$.
--
--   **Formalization Note** With no requests there is nothing to serve, so a schedule is pinned only at time $0$; the set whose infimum defines the work function is therefore the singleton $\{\mathrm{moveCost}(C_0,X)\}$, consisting of the cost of the single final repositioning move.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, the bootstrapping value w_0(X) = d(C_0, X) used in the dynamic-programming computation of work functions following equation (4); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_nil (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (X : Config k M) : workFn C₀ [] X = moveCost C₀ X := by sorry

end KServer
