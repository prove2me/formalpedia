-- Prove2me | Theorems.Thm_LinearChoresCLS_cls_membership
-- name    : LinearChoresCLS.cls_membership
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:48:17.444502+00:00
-- url     : https://prove2.me/theorems/9cf38925-8549-4141-bc4c-6c735dd3dda0
-- title:
--   CLS membership of linear chores CE (Chaudhury, Garg, McGlaughlin, Mehta 2022)
-- statement:
--   Computing a competitive equilibrium of a linear Fisher market with chores lies in CLS: for some fixed exponent $k$, the problem with answers of encoding length at most $(|x|+1)^k+k$ is total, has polynomial-time checkable answers, and reduces in polynomial time to 3D-Continuous-Localopt.
--
--   This is the cited membership half of Theorem 1.1 (Chaudhury, Garg, McGlaughlin and Mehta, 2022, with $\mathrm{PPAD}\cap\mathrm{PLS}=\mathrm{CLS}$ by Fearnley, Goldberg, Hollender and Savani, 2023).
--
--   **Formalization Note** CLS is the public class `InCLS`, and the answer bound is the public `bounded`.
--
--   Differences from the source:
--   - reading: "computing a CE lies in PPAD ∩ PLS = CLS" → ∃ k, InCLS (bounded choresCESearch k); reason: membership of a search problem in CLS requires polynomially bounded answers; the exponent is chosen before all instances
-- source:
--   Liu–Ma–Tao–Yang–Zheng, Competitive Equilibrium for Linear Chores is CLS-complete, arXiv:2611.06589 (held version, sha256 85d34a9e048d151ecff70a8614b9c2dd44307d5cf60faba74d14b2dd7eedc0b5), pp.3–4 (cited: Chaudhury, Garg, McGlaughlin, Mehta 2022; Fearnley, Goldberg, Hollender, Savani 2023)

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity
import Definitions.Def_LinearChoresCLS_ChoresSearch

open NetworkEquilibriumCLS.LinearNash

namespace LinearChoresCLS

/-- **CLS membership** (arXiv:2611.06589, held version sha256 85d34a9e…, p.3 and p.4; cited from
Chaudhury, Garg, McGlaughlin and Mehta 2022, with CLS = PPAD ∩ PLS, Fearnley et al. 2023):
computing a competitive equilibrium of a linear Fisher market with chores lies in CLS. For some
fixed answer-length exponent `k`, the problem with answers of length at most `(|x| + 1)^k + k` is
total, polynomially checkable, and reduces to 3D-Continuous-Localopt.

**Formalization Note.** CLS is the public class `InCLS`; the bound is the public `bounded`. -/
theorem cls_membership : ∃ k : ℕ, InCLS (bounded choresCESearch k) := by sorry

end LinearChoresCLS
