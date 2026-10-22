-- Prove2me | Theorems.Thm_JobShopLTAS_Core_restrictedOpt_le
-- name    : JobShopLTAS.Core.restrictedOpt_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:24:49.043783+00:00
-- url     : https://prove2.me/theorems/3bc572c3-2dde-4b47-bf75-c1e6fe1cc7b3
-- title:
--   Section 2.1, p. 291 — restricting big operations to the grid costs at most $\mu m\varepsilon P_{\max}$
-- statement:
--   Let $m\ge 2$, $\mu\ge 1$, $0<\varepsilon<1$, $\varepsilon^{\lceil m/\varepsilon\rceil}\le\alpha\le\varepsilon$ and $P_{\max}>0$. Then feasible restricted schedules of the jobs $B\cup T$ exist, and the restricted optimum satisfies
--   $$\widetilde C^*_{\max}\le C^*_{\max}+\mu m\varepsilon P_{\max}\le(1+\mu m\varepsilon)\,C^*_{\max}.$$
--   Here $\widetilde C^*_{\max}$ is the infimum of the makespans of the feasible schedules of $B\cup T$ in which every big operation starts at the beginning of an interval of the first type, and $C^*_{\max}$ is the optimum makespan of the whole instance (all $n$ jobs).
--
--   The restricted problem is the one the rest of the paper's algorithm solves, and this bound is what makes that restriction affordable.
--
--   **Formalization Note.** The existence clause is what makes $\widetilde C^*_{\max}$ (an infimum) a genuine optimum value rather than the junk value of an empty infimum. $C^*_{\max}$ on the right is that of the full job set; the paper uses the same symbol without distinguishing it from the optimum of $B\cup T$, which is no larger.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 291, Section 2.1

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem

namespace JobShopLTAS.Core

/-- §2.1, p. 291: restricted schedules exist, and
`C̃*_max ≤ C*_max + µmεP_max ≤ (1 + µmε) C*_max`, where `C̃*_max` is the optimum over
restricted schedules of `B ∪ T` and `C*_max` the optimum of the whole instance. -/
theorem restrictedOpt_le {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax) :
    (∃ s : inst.Op → ℝ,
        inst.IsFeasibleSchedule (inst.bigJobs α ∪ inst.tinyJobs ε α) s ∧
        inst.IsRestricted ε α s) ∧
      inst.restrictedOpt ε α ≤
        inst.optMakespan Finset.univ + (inst.maxOps : ℝ) * m * ε * inst.Pmax ∧
      inst.optMakespan Finset.univ + (inst.maxOps : ℝ) * m * ε * inst.Pmax ≤
        (1 + (inst.maxOps : ℝ) * m * ε) * inst.optMakespan Finset.univ := by sorry

end JobShopLTAS.Core
