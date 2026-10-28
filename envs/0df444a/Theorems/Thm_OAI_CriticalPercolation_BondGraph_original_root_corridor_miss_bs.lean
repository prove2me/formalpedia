-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_original_root_corridor_miss_bs
-- name    : OAI.CriticalPercolation.BondGraph.original_root_corridor_miss_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:27:38.843561+00:00
-- url     : https://prove2.me/theorems/e89effab-a891-4366-8459-33b9484fcbad
-- title:
--   OAI.CriticalPercolation.BondGraph.original_root_corridor_miss_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.original_root_corridor_miss` of [lean/OAI/Probability/CriticalPercolation/ProductMeasure/SourceMissLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/ProductMeasure/SourceMissLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory`, `open scoped Classical ENNReal`, `open BernoulliProduct`):
--
--   ```lean
--   theorem original_root_corridor_miss_bs (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
--       (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ) (U : Set E)
--       (hDU : G.inducedEdges (relayDomain t z J (L+1/2) σ)⊆U)
--       (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
--       (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
--       (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
--       (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
--       (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
--       (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
--       (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
--       (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
--       (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
--       (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
--       (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
--       (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
--       (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
--       (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
--         (G.coordinateMove t z m e y s)) :
--       (BernoulliProduct.law (fun _ : E => p')).real
--         (G.restrictedSeed (G.vertexBall o m) (relayMark t z (L+1/2) σ ρ) U)ᶜ ≤ η+L*κ
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BernoulliProduct.law`, `OAI.CriticalPercolation.BondGraph.LocallyFinite`, `OAI.CriticalPercolation.BondGraph.coordinateMove`, `OAI.CriticalPercolation.BondGraph.fullGraph`, `OAI.CriticalPercolation.BondGraph.incidentEdges`, `OAI.CriticalPercolation.BondGraph.inducedEdges`, `OAI.CriticalPercolation.BondGraph.relayDomain`, `OAI.CriticalPercolation.BondGraph.relayMark`, `OAI.CriticalPercolation.BondGraph.restrictedSeed` and `OAI.CriticalPercolation.BondGraph.vertexBall` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BondGraph.approximate_moves_contradiction_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/ProductMeasure/SourceMissLaw.lean (declaration OAI.CriticalPercolation.BondGraph.original_root_corridor_miss)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
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
open BernoulliProduct

variable {V E : Type*} [Countable V] [Countable E] (G : BondGraph V E)

theorem original_root_corridor_miss_bs (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o : V) (t z : V → ℝ) (σ e ρ J : ℝ) (L R m : ℕ) (U : Set E)
    (hDU : G.inducedEdges (relayDomain t z J (L+1/2) σ)⊆U)
    (hσ : |σ|=1) (he : 0<e) (hρ : 0 ≤ ρ) (hJ : 26200<J) (hL : 416 ≤ L)
    (heL : (L+3)*e<1/100) (hr : (R+m+1)*ρ<e/10) (hto : t o=0) (hzo : z o=0)
    (ht : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |t u-t v| ≤ ρ)
    (hz : ∀ ⦃u v⦄, G.fullGraph.Adj u v → |z u-z v| ≤ ρ)
    (hcR : m<R) (pc p' : unitInterval) (hpc₀ : 0<(pc : ℝ)) (hpc : (pc : ℝ)<1)
    (hpp : (pc : ℝ)/2 ≤ p') (hppc : (p' : ℝ) ≤ pc)
    (D k M VM : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard ≤ D)
    (hM : 0<M) (hMbound : ∀ v, (G.vertexBall v (4*m+2)).ncard ≤ M)
    (hVM : ∀ v, (G.vertexBall v m).ncard ≤ VM)
    (κ η : ℝ) (hκ : 0<κ) (hκ1 : κ ≤ 1) (hη₀ : 0 ≤ η)
    (hη : η ≤ κ*(κ/4)/(4*(Real.log (4/κ)+1)))
    (hk : M*⌈Real.log (4/κ)/((pc : ℝ)/2)^(m+1+VM)⌉₊ ≤ k)
    (hR : 4/(κ*(1-(pc : ℝ))^(D*k))<(R : ℝ)-m)
    (hmove : ∀ y s, |s|=1 → 1-η ≤ (BernoulliProduct.law (fun _ : E => p')).real
      (G.coordinateMove t z m e y s)) :
    (BernoulliProduct.law (fun _ : E => p')).real
      (G.restrictedSeed (G.vertexBall o m) (relayMark t z (L+1/2) σ ρ) U)ᶜ ≤ η+L*κ := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
