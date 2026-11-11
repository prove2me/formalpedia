-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_fresh_collar_transfer
-- name    : OAI.CriticalPercolation.BondGraph.fresh_collar_transfer
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:19:45.638663+00:00
-- url     : https://prove2.me/theorems/5d881f23-f0fd-4846-968c-c85f1897fbea
-- title:
--   OAI.CriticalPercolation.BondGraph.fresh_collar_transfer: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.fresh_collar_transfer` of [lean/OAI/Probability/CriticalPercolation/Gluing/FreshCollarExact.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/FreshCollarExact.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open BernoulliProduct`):
--
--   ```lean
--   theorem fresh_collar_transfer (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
--       (m R : ℕ) (hcR : m<R) (Dstar : Set E)
--       (houtside : ∀ a∈A, a∉G.vertexCollar Input R)
--       (hregion : G.inducedEdges (G.vertexCollar Input R)⊆Dstar)
--       (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
--       (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
--       (hq : ∀ e∈Dstar, q (Sum.inl e)=p')
--       (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
--       (hM : 0 < M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
--       (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
--       (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (hη₀ : 0≤η)
--       (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
--       (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
--       (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
--       (hmean : ∀ y∈G.vertexCollar Input R,
--         1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
--           ((forceOn Dstarᶜ ∅) ⁻¹' G.seedHitEvent (G.vertexBall y m) T)) :
--       (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
--         (G.withSource A).hitEvent none (some '' T)) ≤ κ
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BernoulliProduct.forceOn`, `OAI.CriticalPercolation.BernoulliProduct.law`, `OAI.CriticalPercolation.BondGraph.hitEvent`, `OAI.CriticalPercolation.BondGraph.incidentEdges`, `OAI.CriticalPercolation.BondGraph.inducedEdges`, `OAI.CriticalPercolation.BondGraph.seedHitEvent`, `OAI.CriticalPercolation.BondGraph.vertexBall`, `OAI.CriticalPercolation.BondGraph.vertexCollar` and `OAI.CriticalPercolation.BondGraph.withSource` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BondGraph.LocallyFinite` and `OAI.CriticalPercolation.BondGraph.fullGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.root_corridor_miss` and `OAI.CriticalPercolation.Corridor.CoordinateData.prospective_estimate` of this split import it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/FreshCollarExact.lean (declaration OAI.CriticalPercolation.BondGraph.fresh_collar_transfer)

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
open scoped Classical BigOperators ENNReal

namespace CriticalPercolation.BondGraph
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem fresh_collar_transfer (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (A Input T : Set V) (hA : A.Finite) (q : (E⊕A) → unitInterval)
    (m R : ℕ) (hcR : m<R) (Dstar : Set E)
    (houtside : ∀ a∈A, a∉G.vertexCollar Input R)
    (hregion : G.inducedEdges (G.vertexCollar Input R)⊆Dstar)
    (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (hq : ∀ e∈Dstar, q (Sum.inl e)=p')
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0 < M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ≤1) (hη₀ : 0≤η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmean : ∀ y∈G.vertexCollar Input R,
      1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
        ((forceOn Dstarᶜ ∅) ⁻¹' G.seedHitEvent (G.vertexBall y m) T)) :
    (BernoulliProduct.law q).real ((G.withSource A).hitEvent none (some '' Input)\
      (G.withSource A).hitEvent none (some '' T)) ≤ κ := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
