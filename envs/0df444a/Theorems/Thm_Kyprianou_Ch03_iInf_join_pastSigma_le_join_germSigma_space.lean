-- Prove2me | Theorems.Thm_Kyprianou_Ch03_iInf_join_pastSigma_le_join_germSigma_space
-- name    : Kyprianou.Ch03.iInf_join_pastSigma_le_join_germSigma_space
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T05:16:20.458907+00:00
-- url     : https://prove2.me/theorems/0ea826b7-cceb-49dd-8797-f6551c18a604
-- title:
--   Space-level Inf-join of past towers is below join-germ
-- statement:
--   For a sub-$\sigma$-algebra $G$ and process $Y$,
--
--   $$\bigwedge_{\varepsilon>0}(G\vee\mathrm{pastSigma}\,Y\,\varepsilon)\le G\vee\mathrm{germSigma}\,Y.$$
--
--   This is the space-level form of the setwise Inf-join lattice step.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem iInf_join_pastSigma_le_join_germSigma_space
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real) :
    (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) ≤ G ⊔ germSigma Y := by
  sorry
end Kyprianou.Ch03
