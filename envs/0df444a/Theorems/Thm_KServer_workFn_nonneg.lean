-- Prove2me | Theorems.Thm_KServer_workFn_nonneg
-- name    : KServer.workFn_nonneg
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:16:44.691411+00:00
-- url     : https://prove2.me/theorems/2899efb6-f132-4464-912f-26e2d9be152b
-- title:
--   The work function is nonnegative
-- statement:
--   Every value of the work function is nonnegative:
--   $$0\;\le\;w(C_0;\sigma;X).$$
--
--   **Role.** The work function is defined as an infimum of schedule costs, and in the reals the infimum of the empty set is $0$ by convention, so this is not idle bookkeeping: it records both that the set of schedules is nonempty — which is where $k\ge1$ is used — and that every schedule cost is a sum of distances. It is the first fact every argument about work functions consumes.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, the properties of work functions listed after equation (4) (property the well-definedness of the infimum in equation (4)); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_nonneg (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) : 0 ≤ workFn C₀ σ X := by sorry

end KServer
