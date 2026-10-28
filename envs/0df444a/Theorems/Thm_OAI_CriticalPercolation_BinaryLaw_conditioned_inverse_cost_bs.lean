-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_inverse_cost_bs
-- name    : OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:33:49.054425+00:00
-- url     : https://prove2.me/theorems/994a8fa0-403d-410d-9084-a459cdadf1e6
-- title:
--   OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost` of [lean/OAI/Probability/CriticalPercolation/Entropy/BinaryInverseCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryInverseCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BinaryLaw`, with `open scoped Classical`, `open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy`):
--
--   ```lean
--   theorem conditioned_inverse_cost_bs (horder : LazyDFS.GoodDarts G order)
--       (ho : LazyDFS.Exhaustive G order) (hd : 0 < d) (hp : p ∈ Set.Ioo 0 1)
--       (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
--       {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
--       (hconn : ∀ j, 0 < j → j < d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
--       (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
--       (hD : 0 < descriptorMass G order d x p w s n D) :
--       let Q := conditionedMass G order d x p w s n D
--       let L := constructionCost G order d x p w c s n D
--       (∑ i ∈ activeSteps n D, ∑ z, Q z * Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) ≤
--         (16/(2*p*(1-p)))*(2*L+n*Real.log 4) + 2*L+2*n*Real.log 4
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BinaryLaw.FixedDescriptor`, `OAI.CriticalPercolation.BinaryLaw.activeSteps`, `OAI.CriticalPercolation.BinaryLaw.conditionedMass`, `OAI.CriticalPercolation.BinaryLaw.constructionCost`, `OAI.CriticalPercolation.BinaryLaw.descriptorMass`, `OAI.CriticalPercolation.BinaryLaw.endpointEvent`, `OAI.CriticalPercolation.BinaryLaw.inverseCostFinDec`, `OAI.CriticalPercolation.BinaryLaw.selectedCost`, `OAI.CriticalPercolation.BondGraph.openGraph`, `OAI.CriticalPercolation.FiniteProduct.prob` and `OAI.CriticalPercolation.LazyDFS.Dart` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.LazyDFS.Exhaustive` and `OAI.CriticalPercolation.LazyDFS.GoodDarts` (definitions bundle `OAIQ078B002` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BinaryLaw.conditioned_event_bound_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryInverseCost.lean (declaration OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost)

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
open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy

variable {V E : Type*} [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (D : FixedDescriptor n)

noncomputable section Cost

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.inverseCostFinDec
theorem conditioned_inverse_cost_bs (horder : LazyDFS.GoodDarts G order)
    (ho : LazyDFS.Exhaustive G order) (hd : 0 < d) (hp : p ∈ Set.Ioo 0 1)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hconn : ∀ j, 0 < j → j < d → c ≤ prob w (fun ω => (G.openGraph ω).Reachable (x 0) (x j)))
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let Q := conditionedMass G order d x p w s n D
    let L := constructionCost G order d x p w c s n D
    (∑ i ∈ activeSteps n D, ∑ z, Q z * Real.log (1+selectedCost G order d x p w n D i z.1 (z.2 i))) ≤
      (16/(2*p*(1-p)))*(2*L+n*Real.log 4) + 2*L+2*n*Real.log 4 := by
  sorry

end Cost
end CriticalPercolation.BinaryLaw
end
end

end OAI
end
