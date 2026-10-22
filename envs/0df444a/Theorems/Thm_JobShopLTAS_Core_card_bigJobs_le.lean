-- Prove2me | Theorems.Thm_JobShopLTAS_Core_card_bigJobs_le
-- name    : JobShopLTAS.Core.card_bigJobs_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:09:37.710208+00:00
-- url     : https://prove2.me/theorems/510f9968-1757-4dff-9915-8a7db1e3d38e
-- title:
--   Section 2.1, p. 291 — the number of big jobs: $|B|\le m/\alpha\le m\varepsilon^{-\lceil m/\varepsilon\rceil}$
-- statement:
--   Let $m\ge 2$, $\mu\ge 1$, $0<\varepsilon<1$, $\varepsilon^{\lceil m/\varepsilon\rceil}\le\alpha\le\varepsilon$ and $P_{\max}>0$. The set $B=\{J_j\mid l_j\ge\alpha P_{\max}\}$ of big jobs satisfies
--   $$|B|\le \frac{m}{\alpha}\le m\,\varepsilon^{-\lceil m/\varepsilon\rceil}.$$
--   So the number of big jobs is bounded by a constant depending only on $\varepsilon$ and $m$.
--
--   **Formalization Note.** $P_{\max}>0$ is implicit in the paper: if all processing times are $0$, every job is big and the bound fails.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 291, Section 2.1

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem

namespace JobShopLTAS.Core

/-- §2.1, p. 291: `|B| ≤ m/α ≤ m ε^{-⌈m/ε⌉}`. -/
theorem card_bigJobs_le {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax) :
    ((inst.bigJobs α).card : ℝ) ≤ (m : ℝ) / α ∧
      (m : ℝ) / α ≤ (m : ℝ) * (ε ^ ⌈(m : ℝ) / ε⌉₊)⁻¹ := by sorry

end JobShopLTAS.Core
