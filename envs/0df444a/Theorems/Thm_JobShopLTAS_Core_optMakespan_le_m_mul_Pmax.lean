-- Prove2me | Theorems.Thm_JobShopLTAS_Core_optMakespan_le_m_mul_Pmax
-- name    : JobShopLTAS.Core.optMakespan_le_m_mul_Pmax
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:41:07.486727+00:00
-- url     : https://prove2.me/theorems/77e8bbf9-90cb-487d-824c-9af76c377d0f
-- title:
--   Section 2.1, p. 291 — $mP_{\max}$ bounds the optimum makespan
-- statement:
--   For every job shop instance with $m$ machines,
--   $$C^*_{\max}\le m\,P_{\max}.$$
--   This places the optimum inside the horizon $[0,(1+\mu m\varepsilon)mP_{\max}]$ on which the intervals of the first type and the linear program of the paper are defined.
--
--   **Formalization Note.** The statement carries no hypotheses: it holds for every instance, including $m\ge 2$ and $\mu\ge 1$ assumed in Section 2.1.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 291, Section 2.1

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance

namespace JobShopLTAS.Core

/-- §2.1, p. 291: "`m P_max` is an upper bound on the length of an optimum schedule." -/
theorem optMakespan_le_m_mul_Pmax {m n : ℕ} (inst : Instance m n) :
    inst.optMakespan Finset.univ ≤ (m : ℝ) * inst.Pmax := by sorry

end JobShopLTAS.Core
