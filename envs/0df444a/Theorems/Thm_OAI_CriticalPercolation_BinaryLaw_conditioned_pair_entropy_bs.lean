-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_conditioned_pair_entropy_bs
-- name    : OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy_bs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T13:36:44.98425+00:00
-- url     : https://prove2.me/theorems/9b46c0ec-84b1-4df9-b583-fd96fb77b6f8
-- title:
--   OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy_bs: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.BenjaminiSchramm.cayley_main`, `OAI.Percolation.BenjaminiSchramm.critical_laws` and `OAI.Percolation.BenjaminiSchramm.full_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy` of [lean/OAI/Probability/CriticalPercolation/Entropy/BinaryPairs.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryPairs.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BinaryLaw`, with `open scoped Classical`, `open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy`):
--
--   ```lean
--   theorem conditioned_pair_entropy_bs (D : FixedDescriptor n)
--       (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
--       (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
--       (hD : 0 < descriptorMass G order d x p w s n D) :
--       let P := pushMass Prod.fst (conditionedMass G order d x p w s n D)
--       (∑ i : ActiveIndex n D,
--         divergence (pushMass (pair G (activeLeft (E := E) d x n D i)
--           (activeRight (E := E) d x n D i)).bare.run P)
--         ((pair G (activeLeft (E := E) d x n D i) (activeRight (E := E) d x n D i)).bare.reference p)) ≤
--         16/(2*p*(1-p)) * divergence P (FiniteProduct.density (QueryTree.bitWeight p))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BondGraph`, `OAI.CriticalPercolation.BinaryLaw.ActiveIndex`, `OAI.CriticalPercolation.BinaryLaw.FixedDescriptor`, `OAI.CriticalPercolation.BinaryLaw.activeLeft`, `OAI.CriticalPercolation.BinaryLaw.activeRight`, `OAI.CriticalPercolation.BinaryLaw.conditionedMass`, `OAI.CriticalPercolation.BinaryLaw.descriptorMass`, `OAI.CriticalPercolation.BinaryLaw.endpointEvent`, `OAI.CriticalPercolation.BinaryLaw.pairsClassicalFinDecidable`, `OAI.CriticalPercolation.ExactExposure.State`, `OAI.CriticalPercolation.ExactExposure.pair`, `OAI.CriticalPercolation.FiniteEntropy.pushMass`, `OAI.CriticalPercolation.FiniteProduct.density`, `OAI.CriticalPercolation.FiniteProduct.prob`, `OAI.CriticalPercolation.LazyDFS.Dart`, `OAI.CriticalPercolation.QueryTree.Leaf`, `OAI.CriticalPercolation.QueryTree.bitWeight`, `OAI.CriticalPercolation.QueryTree.run` and `OAI.CriticalPercolation.SearchTree.bare` (definitions bundle `OAIQ078B000` of this split); `OAI.CriticalPercolation.FiniteEntropy.divergence` (definitions bundle `OAIQ078B001` of this split); `OAI.CriticalPercolation.QueryTree.leafFintype` and `OAI.CriticalPercolation.QueryTree.reference` (definitions bundle `OAIQ078B002` of this split).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost_bs` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryPairs.lean (declaration OAI.CriticalPercolation.BinaryLaw.conditioned_pair_entropy)

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

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype I]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (s n : ℕ) (h : History E n) (ω : E → Bool)

noncomputable section Entropy

attribute [local instance] OAI.CriticalPercolation.BinaryLaw.pairsClassicalFinDecidable
omit [Fintype I] in

theorem conditioned_pair_entropy_bs (D : FixedDescriptor n)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (hδ : 0 < prob w (endpointEvent G (x 0) (x d) s))
    (hD : 0 < descriptorMass G order d x p w s n D) :
    let P := pushMass Prod.fst (conditionedMass G order d x p w s n D)
    (∑ i : ActiveIndex n D,
      divergence (pushMass (pair G (activeLeft (E := E) d x n D i)
        (activeRight (E := E) d x n D i)).bare.run P)
      ((pair G (activeLeft (E := E) d x n D i) (activeRight (E := E) d x n D i)).bare.reference p)) ≤
      16/(2*p*(1-p)) * divergence P (FiniteProduct.density (QueryTree.bitWeight p)) := by
  sorry

end Entropy
end CriticalPercolation.BinaryLaw
end
end

end OAI
end
