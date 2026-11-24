-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exists_piSystem_iInf_join_pastSigma_in_join_germ
-- name    : Kyprianou.Ch03.exists_piSystem_iInf_join_pastSigma_in_join_germ
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-24T05:30:20.845929+00:00
-- url     : https://prove2.me/theorems/08f74e80-d24c-4c4f-858c-8b77cf2fb606
-- title:
--   Exists $\pi$-system for Inf-join inside join-germ
-- statement:
--   For a sub-$\sigma$-algebra $G$ and process $Y$, there exists a $\pi$-system $C$ such that
--
--   $$\sigma(C)=\bigwedge_{\varepsilon>0}(G\vee\mathrm{pastSigma}\,Y\,\varepsilon)$$
--
--   and every $s\in C$ is measurable for $G\vee\mathrm{germSigma}\,Y$.
--
--   This packages the Dynkin membership step for the space-level Inf-join lattice inequality.

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem exists_piSystem_iInf_join_pastSigma_in_join_germ
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real) :
    ∃ C : Set (Set Omega),
      IsPiSystem C ∧
        MeasurableSpace.generateFrom C =
          (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε) ∧
          (∀ s ∈ C, @MeasurableSet Omega (G ⊔ germSigma Y) s) := by
  sorry
end Kyprianou.Ch03
