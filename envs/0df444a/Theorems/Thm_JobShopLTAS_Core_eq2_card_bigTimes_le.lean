-- Prove2me | Theorems.Thm_JobShopLTAS_Core_eq2_card_bigTimes_le
-- name    : JobShopLTAS.Core.eq2_card_bigTimes_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T08:38:05.059984+00:00
-- url     : https://prove2.me/theorems/a789ade2-1049-4df8-9b03-d59d41f6fb62
-- title:
--   Section 2.2, Eq. (2) — $|A|\le 2\mu|B|\le 2\mu m/\alpha$
-- statement:
--   Let $m\ge 2$, $\mu\ge 1$, $0<\varepsilon<1$, $\varepsilon^{\lceil m/\varepsilon\rceil}\le\alpha\le\varepsilon$ and $P_{\max}>0$, and fix a feasible restricted schedule of the big operations. The set $A$ of starting and completion times of the big operations satisfies
--   $$|A|\le 2\mu|B|\le \frac{2\mu m}{\alpha}.\tag{2}$$
--   So the number of intervals of the second type, $|A|+1$, is bounded by a constant depending only on $\varepsilon$, $m$ and $\mu$.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 292, Section 2.2, Eq. (2)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem
import Definitions.Def_JobShopLTAS_Core_IntervalLP

namespace JobShopLTAS.Core

/-- §2.2, Eq. (2), p. 292: for a feasible restricted schedule `σ` of the big operations, the
set `A` of their starting and completion times satisfies `|A| ≤ 2µ|B| ≤ 2µm/α`. -/
theorem eq2_card_bigTimes_le {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax)
    (σ : inst.Op → ℝ) (hσ : inst.IsBigSchedule ε α σ) :
    ((inst.bigTimes α σ).card : ℝ) ≤ 2 * (inst.maxOps : ℝ) * (inst.bigJobs α).card ∧
      2 * (inst.maxOps : ℝ) * (inst.bigJobs α).card ≤ 2 * (inst.maxOps : ℝ) * m / α := by sorry

end JobShopLTAS.Core
