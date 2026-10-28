-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BondGraph_fresh_contact_transfer_bs
-- name    : OAI.CriticalPercolation.BondGraph.fresh_contact_transfer_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:25:23.349334+00:00
-- url     : https://prove2.me/theorems/5a578bce-d0de-4208-8b15-e6e035fe12e3
-- title:
--   OAI.CriticalPercolation.BondGraph.fresh_contact_transfer_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BondGraph.fresh_contact_transfer` of [lean/OAI/Probability/CriticalPercolation/Gluing/FreshContactTransfer.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/FreshContactTransfer.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BondGraph`, with `open Set Function MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open BernoulliProduct`):
--
--   ```lean
--   theorem fresh_contact_transfer_bs (q : E → unitInterval) (X Y : Set E)
--       (hXY : Disjoint X Y) (d : Set E → Finset V) (F : V → Set E)
--       (B : V → Set V) (L T Input : Set V) (o : V)
--       (hd : ∀ U, MeasurableSet[blockSigma X] {ω | d ω=U})
--       (hF : ∀ v, F v ⊆ Y)
--       (hconnect : ∀ v∈L, ∀ b∈B v, (G.openGraph (F v)).Reachable v b)
--       (C Small : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
--       (hinput : G.hitEvent o Input ⊆ Small∪C)
--       (hcontact : ∀ ω∈C, ∀ v∈d ω, v∈L ∧ (G.openGraph ω).Reachable o v)
--       (K η lam : ℝ) (hK : 0 ≤ K+1) (hη : 0 ≤ η) (hlam : 0 < lam)
--       (hmean : ∀ v∈L, 1-η ≤ (BernoulliProduct.law q).real (G.seedHitEvent (B v) T))
--       (hdis : ∀ σ∈C, (d σ : Set V).Pairwise (fun v w => Disjoint (F v) (F w)))
--       (hs : ∀ σ∈C, K ≤ ∑ v∈d σ, (BernoulliProduct.law q).real (allOpen (F v)))
--       (hs' : ∀ σ∈C, (∑ v∈d σ, (BernoulliProduct.law q).real (allOpen (F v))) ≤ K+1) :
--       (BernoulliProduct.law q).real (G.hitEvent o Input\G.hitEvent o T) ≤
--         (BernoulliProduct.law q).real Small+Real.exp (-K)+(K+1)*η/lam+lam
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BernoulliProduct.allOpen`, `OAI.CriticalPercolation.BernoulliProduct.blockSigma`, `OAI.CriticalPercolation.BernoulliProduct.law`, `OAI.CriticalPercolation.BondGraph.hitEvent`, `OAI.CriticalPercolation.BondGraph.openGraph` and `OAI.CriticalPercolation.BondGraph.seedHitEvent` (definitions bundle `OAIQ078B000` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BondGraph.coordinate_pinned_corridor_failure_bs` and `OAI.CriticalPercolation.BondGraph.original_root_corridor_miss_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Gluing/FreshContactTransfer.lean (declaration OAI.CriticalPercolation.BondGraph.fresh_contact_transfer)

import Mathlib
import Definitions.Def_OAIQ078B000

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action
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

variable {E V : Type*} [Countable E] [Countable V] (G : BondGraph V E)

theorem fresh_contact_transfer_bs (q : E → unitInterval) (X Y : Set E)
    (hXY : Disjoint X Y) (d : Set E → Finset V) (F : V → Set E)
    (B : V → Set V) (L T Input : Set V) (o : V)
    (hd : ∀ U, MeasurableSet[blockSigma X] {ω | d ω=U})
    (hF : ∀ v, F v ⊆ Y)
    (hconnect : ∀ v∈L, ∀ b∈B v, (G.openGraph (F v)).Reachable v b)
    (C Small : Set (Set E)) (hC : MeasurableSet[blockSigma X] C)
    (hinput : G.hitEvent o Input ⊆ Small∪C)
    (hcontact : ∀ ω∈C, ∀ v∈d ω, v∈L ∧ (G.openGraph ω).Reachable o v)
    (K η lam : ℝ) (hK : 0 ≤ K+1) (hη : 0 ≤ η) (hlam : 0 < lam)
    (hmean : ∀ v∈L, 1-η ≤ (BernoulliProduct.law q).real (G.seedHitEvent (B v) T))
    (hdis : ∀ σ∈C, (d σ : Set V).Pairwise (fun v w => Disjoint (F v) (F w)))
    (hs : ∀ σ∈C, K ≤ ∑ v∈d σ, (BernoulliProduct.law q).real (allOpen (F v)))
    (hs' : ∀ σ∈C, (∑ v∈d σ, (BernoulliProduct.law q).real (allOpen (F v))) ≤ K+1) :
    (BernoulliProduct.law q).real (G.hitEvent o Input\G.hitEvent o T) ≤
      (BernoulliProduct.law q).real Small+Real.exp (-K)+(K+1)*η/lam+lam := by
  sorry

end CriticalPercolation.BondGraph
end
end
end

end OAI
end
