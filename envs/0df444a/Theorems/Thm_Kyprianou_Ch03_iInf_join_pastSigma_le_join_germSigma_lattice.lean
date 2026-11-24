-- Prove2me | Theorems.Thm_Kyprianou_Ch03_iInf_join_pastSigma_le_join_germSigma_lattice
-- name    : Kyprianou.Ch03.iInf_join_pastSigma_le_join_germSigma_lattice
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-24T10:02:45.68138+00:00
-- url     : https://prove2.me/theorems/6f37bd26-9725-47dd-a8c5-f6185a654543
-- title:
--   Lattice Inf-join of past towers below join-germ
-- statement:
--   For a sub-$\sigma$-algebra $G$ and process $Y$,
--
--   $$\bigwedge_{\varepsilon>0}(G\vee\mathrm{pastSigma}\,Y\,\varepsilon)\le G\vee\mathrm{germSigma}\,Y.$$
--
--   Williams-sensitive lattice core for the Dynkin $\pi$-system packaging.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem iInf_join_pastSigma_le_join_germSigma_lattice
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real) :
    (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) ≤ G ⊔ germSigma Y := by
  sorry
end Kyprianou.Ch03
