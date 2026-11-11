-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_root_corridor_miss
-- name    : OAI.CriticalPercolation.BondGraph.root_corridor_miss
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:20:42.721086+00:00
-- url     : https://prove2.me/theorems/423066b0-527a-4d58-97b3-1034f9924fcf
-- title:
--   OAI.CriticalPercolation.BondGraph.root_corridor_miss: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.root_corridor_miss` of [lean/OAI/Probability/CriticalPercolation/Gluing/RootCorridor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/RootCorridor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory`, `open scoped Classical ENNReal`):
--
--   ```lean
--   theorem root_corridor_miss (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
--       (q : (E⊕G.vertexBall o m) → unitInterval)
--       (hwire : ∀ a : G.vertexBall o m, q (Sum.inr a)=1)
--       (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
--       (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
--       (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
--       (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
--       (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
--       (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
--       (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q (Sum.inl b)=p')
--       (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
--       (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
--       (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
--       (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
--       (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
--       (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
--       (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
--       (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
--         (G.coordinateMove t z m e y s)) :
--       (BernoulliProduct.law q).real
--         ((G.withSource (G.vertexBall o m)).hitEvent none
--           (some '' relayMark t z (L+1/2) σ ρ))ᶜ ≤ η+L*κ
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BernoulliProduct.law`, `OAI.CriticalPercolation.BondGraph.coordinateMove`, `OAI.CriticalPercolation.BondGraph.hitEvent`, `OAI.CriticalPercolation.BondGraph.incidentEdges`, `OAI.CriticalPercolation.BondGraph.inducedEdges`, `OAI.CriticalPercolation.BondGraph.relayDomain`, `OAI.CriticalPercolation.BondGraph.relayMark`, `OAI.CriticalPercolation.BondGraph.vertexBall` and `OAI.CriticalPercolation.BondGraph.withSource` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/RootCorridor.lean (declaration OAI.CriticalPercolation.BondGraph.root_corridor_miss)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Function MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem root_corridor_miss (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ)
    (q : (E⊕G.vertexBall o m) → unitInterval)
    (hwire : ∀ a : G.vertexBall o m, q (Sum.inr a)=1)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ b∈G.inducedEdges (relayDomain t z J (L+1/2) σ), q (Sum.inl b)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law q).real
      ((G.withSource (G.vertexBall o m)).hitEvent none
        (some '' relayMark t z (L+1/2) σ ρ))ᶜ ≤ η+L*κ := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
