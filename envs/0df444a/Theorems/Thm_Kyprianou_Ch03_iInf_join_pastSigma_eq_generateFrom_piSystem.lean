-- Prove2me | Theorems.Thm_Kyprianou_Ch03_iInf_join_pastSigma_eq_generateFrom_piSystem
-- name    : Kyprianou.Ch03.iInf_join_pastSigma_eq_generateFrom_piSystem
-- status  : Open
-- author  : @pageman
-- created : 2026-11-24T04:46:12.418796+00:00
-- url     : https://prove2.me/theorems/2a5b000a-ac0d-4241-929e-07b4d5896423
-- title:
--   Inf-join of past towers equals generateFrom of a $\pi$-system
-- statement:
--   For any sub-$\sigma$-algebra $G$ and process $Y$, there exists a $\pi$-system $C$ such that
--
--   $$\sigma(C)=\bigwedge_{\varepsilon>0}(G\vee\mathrm{pastSigma}\,Y\,\varepsilon).$$
--
--   This is Dynkin step 1 for the germ Inf-join lattice identity.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem iInf_join_pastSigma_eq_generateFrom_piSystem
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real) :
    ∃ C : Set (Set Omega),
      IsPiSystem C ∧
        MeasurableSpace.generateFrom C =
          (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) := by
  sorry
end Kyprianou.Ch03
