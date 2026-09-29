-- Prove2me | Theorems.Thm_KServer_workFn_mono
-- name    : KServer.workFn_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:17:54.120689+00:00
-- url     : https://prove2.me/theorems/f590e27f-b187-4bed-bbc4-1b5299b34ce1
-- title:
--   The work function does not decrease as requests arrive
-- statement:
--   Serving one more request never lowers the work function: for every request $r$,
--   $$w(C_0;\sigma;X)\;\le\;w(C_0;\sigma\cdot r;X).$$
--
--   **Role.** This is the third of the standard properties. It says the work function increases pointwise in time, which is what makes the increments $w_t-w_{t-1}$ the natural currency of the potential-function analyses built on it. The proof drops the last move of a schedule for $\sigma\cdot r$ and appeals to the triangle inequality.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, the properties of work functions listed after equation (4) (property 3); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_mono (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) :
    workFn C₀ σ X ≤ workFn C₀ (σ ++ [r]) X := by sorry

end KServer
