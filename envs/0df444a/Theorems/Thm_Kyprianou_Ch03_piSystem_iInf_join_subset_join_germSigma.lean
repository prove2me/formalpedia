-- Prove2me | Theorems.Thm_Kyprianou_Ch03_piSystem_iInf_join_subset_join_germSigma
-- name    : Kyprianou.Ch03.piSystem_iInf_join_subset_join_germSigma
-- status  : Disproved
-- author  : @pageman
-- created : 2026-11-24T04:46:12.632223+00:00
-- url     : https://prove2.me/theorems/8c7098e0-79b3-4f46-ab05-967a44662f1a
-- title:
--   Inf-join $\pi$-system sits inside $G\vee$ germ
-- statement:
--   If a $\pi$-system $C$ generates $\bigwedge_{\varepsilon>0}(G\vee\mathrm{pastSigma}\,Y\,\varepsilon)$, then every $s\in C$ is measurable for $G\vee\mathrm{germSigma}\,Y$.
--
--   This is Dynkin step 2 ($\pi$-system membership in the join-germ Dynkin system).

import Mathlib
import Definitions.Def_DurrettProbability_Brownian
open MeasureTheory ProbabilityTheory DurrettProbability Set
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem piSystem_iInf_join_subset_join_germSigma
    {Omega : Type} [MeasurableSpace Omega]
    (G : MeasurableSpace Omega)
    (Y : NNReal → Omega → Real)
    (C : Set (Set Omega))
    (hC : IsPiSystem C)
    (hgen : MeasurableSpace.generateFrom C =
      (⨅ ε : NNReal, ⨅ (_ : 0 < ε), G ⊔ pastSigma Y ε)) :
    ∀ s ∈ C, @MeasurableSet Omega (G ⊔ germSigma Y) s := by
  sorry
end Kyprianou.Ch03
