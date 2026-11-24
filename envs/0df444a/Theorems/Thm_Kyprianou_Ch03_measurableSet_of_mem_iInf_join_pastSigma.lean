-- Prove2me | Theorems.Thm_Kyprianou_Ch03_measurableSet_of_mem_iInf_join_pastSigma
-- name    : Kyprianou.Ch03.measurableSet_of_mem_iInf_join_pastSigma
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T05:06:09.174822+00:00
-- url     : https://prove2.me/theorems/c09004c6-b355-47a4-9719-b47278938e31
-- title:
--   Setwise Inf-join measurability implies join-germ measurability
-- statement:
--   Let $G$ be a sub-$\sigma$-algebra and $Y$ a real process. If a set $s$ is measurable for $G\vee\mathrm{pastSigma}\,Y\,\varepsilon$ for every $\varepsilon>0$, then $s$ is measurable for $G\vee\mathrm{germSigma}\,Y$.
--
--   $$(\forall\varepsilon>0,\ s\in G\vee\mathcal{H}_\varepsilon)\implies s\in G\vee\mathcal{H}_{0+}.$$
--
--   This is the setwise form of the Inf-join $\le$ join-germ lattice step.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem measurableSet_of_mem_iInf_join_pastSigma
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real)
    {s : Set Omega}
    (h : ∀ ε : NNReal, 0 < ε → @MeasurableSet Omega (G ⊔ pastSigma Y ε) s) :
    @MeasurableSet Omega (G ⊔ germSigma Y) s := by
  sorry
end Kyprianou.Ch03
