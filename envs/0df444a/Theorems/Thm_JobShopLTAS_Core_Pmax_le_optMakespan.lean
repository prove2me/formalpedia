-- Prove2me | Theorems.Thm_JobShopLTAS_Core_Pmax_le_optMakespan
-- name    : JobShopLTAS.Core.Pmax_le_optMakespan
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:29:35.081981+00:00
-- url     : https://prove2.me/theorems/aafd22f7-33ad-415a-a299-b99d8a775629
-- title:
--   Section 2, p. 290 — $P_{\max}\le C^*_{\max}$
-- statement:
--   For every job shop instance, the maximum machine load is a lower bound on the optimum makespan:
--   $$P_{\max}\le C^*_{\max}.$$
--   Here $P_{\max}=\max_t\sum_{\pi_{ij}=t}p_{ij}$ and $C^*_{\max}$ is the infimum of the makespans of all feasible schedules of all $n$ jobs.
--
--   This is the basic lower bound against which every approximation guarantee in the paper is measured.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 290, Section 2

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

namespace JobShopLTAS.Core

/-- §2, p. 290: "Clearly, `P_max ≤ C*_max`." The maximum machine load is at most the
optimum makespan of the whole instance. -/
theorem Pmax_le_optMakespan {m n : ℕ} (inst : Instance m n) :
    inst.Pmax ≤ inst.optMakespan Finset.univ := by sorry

end JobShopLTAS.Core
