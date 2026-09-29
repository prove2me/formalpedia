-- Prove2me | Theorems.Thm_KServer_workFn_lipschitz
-- name    : KServer.workFn_lipschitz
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:17:20.905209+00:00
-- url     : https://prove2.me/theorems/800aba8f-cc03-4d5c-98de-918c0d0ef6f0
-- title:
--   Work-function values differ by at most the distance of their configurations
-- statement:
--   For all configurations $X$ and $Y$,
--   $$w(C_0;\sigma;X)\;\le\;w(C_0;\sigma;Y)+\mathrm{moveCost}(Y,X).$$
--
--   **Role.** This is the second of the standard properties of work functions: as their values grow they stay close to one another, so on a bounded metric space one may think of $w_t$ as the cost of the optimal algorithm shifted by a bounded amount. Concretely it is what lets an analysis replace one configuration by another inside a work-function value at a controlled price, and the analysis of the Work Function Algorithm uses it at nearly every step. The proof is the obvious one: a schedule ending at $Y$ becomes a schedule ending at $X$ by appending one more move.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, the properties of work functions listed after equation (4) (property 2); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_lipschitz (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X Y : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ σ Y + moveCost Y X := by sorry

end KServer
