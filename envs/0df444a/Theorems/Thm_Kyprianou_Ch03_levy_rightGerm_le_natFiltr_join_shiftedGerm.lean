-- Prove2me | Theorems.Thm_Kyprianou_Ch03_levy_rightGerm_le_natFiltr_join_shiftedGerm
-- name    : Kyprianou.Ch03.levy_rightGerm_le_natFiltr_join_shiftedGerm
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-24T04:06:58.767451+00:00
-- url     : https://prove2.me/theorems/28fb2433-3339-4d06-8543-9a6d47cfca9d
-- title:
--   Right germ sits in past joined with shifted germ
-- statement:
--   Let $X$ be a real process indexed by $\mathbb{R}_{\ge 0}$ and write $\mathcal{G}_u=\sigma(X_s:s\le u)$. Fix $t\ge 0$ and define the shifted increment process $Y_u=X_{t+u}-X_t$. Let $\mathcal{G}_{0+}(Y)$ be the germ $\sigma$-field of $Y$ at time $0$.
--
--   Then
--   $$
--   \bigcap_{s>t}\mathcal{G}_s \;\subseteq\; \mathcal{G}_t\vee\mathcal{G}_{0+}(Y).
--   $$
--
--   This is the structural (pathwise $\sigma$-algebra) half of the Blumenthal reduction for Kyprianou Exercise 3.1.
-- source:
--   Kyprianou (2006), Chapter 3, Exercise 3.1 (structural shift identity), printed p. 83

import Mathlib
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem levy_rightGerm_le_natFiltr_join_shiftedGerm
    {Omega : Type} [MeasurableSpace Omega]
    (X : NNReal -> Omega -> Real)
    (t : NNReal) :
    (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
      PerfCorrMSQ.natFiltr X t ⊔
        germSigma (fun u : NNReal => fun omega : Omega => X (t + u) omega - X t omega) := by
  sorry

end Kyprianou.Ch03
