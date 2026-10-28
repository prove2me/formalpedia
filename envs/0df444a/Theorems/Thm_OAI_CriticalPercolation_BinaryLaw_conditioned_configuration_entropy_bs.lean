-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_configuration_entropy_bs
-- name    : OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:33:19.233306+00:00
-- url     : https://prove2.me/theorems/73172c7b-0ad2-44a9-8ebf-10a8d8b4e01a
-- title:
--   OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy` of [lean/OAI/Probability/CriticalPercolation/Entropy/BinaryConfiguration.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryConfiguration.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BinaryLaw`, with `open scoped Classical`, `open FiniteProduct BondGraph BinaryInterpolation FiniteEntropy ExactExposure`):
--
--   ```lean
--   theorem conditioned_configuration_entropy_bs (ho : LazyDFS.Exhaustive G order)
--       (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
--       (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
--       {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
--       (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
--       (s n : ℕ) (D : FixedDescriptor n)
--       (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
--       (hD : 0 < descriptorMass G order d x p w s n D) :
--       let Q := conditionedMass G order d x p w s n D
--       let a := fun i ω => scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω)
--       divergence (pushMass Prod.fst Q) (FiniteProduct.density (QueryTree.bitWeight p)) ≤
--           2*constructionCost G order d x p w c s n D+n*Real.log 4 ∧
--         (∑ z, Q z * logContactMass a z.1) ≤ constructionCost G order d x p w c s n D+n*Real.log 4
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BinaryLaw.FixedDescriptor`, `OAI.CriticalPercolation.BinaryLaw.classicalFinDecidable`, `OAI.CriticalPercolation.BinaryLaw.conditionedMass`, `OAI.CriticalPercolation.BinaryLaw.constructionCost`, `OAI.CriticalPercolation.BinaryLaw.descriptorMass`, `OAI.CriticalPercolation.BinaryLaw.endpointEvent`, `OAI.CriticalPercolation.BinaryLaw.scheduleWeight`, `OAI.CriticalPercolation.BondGraph.openGraph`, `OAI.CriticalPercolation.ExactExposure.configuration`, `OAI.CriticalPercolation.FiniteEntropy.logContactMass`, `OAI.CriticalPercolation.FiniteEntropy.pushMass`, `OAI.CriticalPercolation.FiniteProduct.density`, `OAI.CriticalPercolation.FiniteProduct.prob`, `OAI.CriticalPercolation.LazyDFS.Dart` and `OAI.CriticalPercolation.QueryTree.bitWeight` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.FiniteEntropy.divergence` (definitions bundle `OAIQ078B001` of this split); `OAI.CriticalPercolation.LazyDFS.Exhaustive` (definitions bundle `OAIQ078B002` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalPercolation.BinaryLaw.conditioned_event_bound_bs` and `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs` of this split import it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryConfiguration.lean (declaration OAI.CriticalPercolation.BinaryLaw.conditioned_configuration_entropy)

import Mathlib
import Definitions.Def_OAIQ078B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability _root_.OAI.CriticalPercolation.BondGraph.orbitalActionGroup_action _root_.OAI.Percolation.PointwisePerm.topology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace CriticalPercolation.BinaryLaw
open scoped Classical
open FiniteProduct BondGraph BinaryInterpolation FiniteEntropy ExactExposure

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ)

noncomputable section EntropyFinal

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.classicalFinDecidable
theorem conditioned_configuration_entropy_bs (ho : LazyDFS.Exhaustive G order)
    (hd : 0<d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c≤1)
    (hconn : ∀ j, 0<j → j<d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (s n : ℕ) (D : FixedDescriptor n)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let Q := conditionedMass G order d x p w s n D
    let a := fun i ω => scheduleWeight G order d x p w n (fun j => (D j).1) i (configuration ω)
    divergence (pushMass Prod.fst Q) (FiniteProduct.density (QueryTree.bitWeight p)) ≤
        2*constructionCost G order d x p w c s n D+n*Real.log 4 ∧
      (∑ z, Q z * logContactMass a z.1) ≤ constructionCost G order d x p w c s n D+n*Real.log 4 := by
  sorry

end EntropyFinal
end CriticalPercolation.BinaryLaw
end
end

end OAI
end
