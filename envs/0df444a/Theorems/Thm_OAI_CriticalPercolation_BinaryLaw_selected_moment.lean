-- Prove2me | Theorems.Thm_OAI_CriticalPercolation_BinaryLaw_selected_moment
-- name    : OAI.CriticalPercolation.BinaryLaw.selected_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T17:23:23.718199+00:00
-- url     : https://prove2.me/theorems/6998eae7-238c-4590-8702-ba418ff4e68b
-- title:
--   OAI.CriticalPercolation.BinaryLaw.selected_moment: intermediate lemma from OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalPercolation.BondGraph.no_percolation_at_criticality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *No percolation at criticality on quasi-transitive graphs (result family 213)*, OpenAI Math Release, September 24, 2026, result family 213, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalPercolation.BinaryLaw.selected_moment` of [lean/OAI/Probability/CriticalPercolation/Entropy/BinaryTranscript.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryTranscript.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalPercolation.BinaryLaw`, with `open scoped Classical`, `open FiniteProduct BondGraph BinaryInterpolation InterpolationForest ExactExposure FiniteEntropy`):
--
--   ```lean
--   lemma selected_moment (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
--       (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
--       (i : Fin n) (hi : i ∈ activeSteps n D) :
--       (∑ ym : (E → Bool) × Option E,
--         pushMass (selectedTranscript G d x n D i) (FiniteProduct.density (QueryTree.bitWeight p)) ym.1 *
--         selectedWeight G order d x p w n D i ym.1 ym.2 *
--           (1+selectedCost G order d x p w n D i ym.1 ym.2)) ≤ 4
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalPercolation.BinaryLaw.FixedDescriptor`, `OAI.CriticalPercolation.BinaryLaw.activeSteps`, `OAI.CriticalPercolation.BinaryLaw.selectedCost`, `OAI.CriticalPercolation.BinaryLaw.selectedTranscript`, `OAI.CriticalPercolation.BinaryLaw.selectedWeight`, `OAI.CriticalPercolation.FiniteEntropy.pushMass`, `OAI.CriticalPercolation.FiniteProduct.density`, `OAI.CriticalPercolation.LazyDFS.Dart` and `OAI.CriticalPercolation.QueryTree.bitWeight` (definitions bundle `OAIQ228B000` of this split); `OAI.CriticalPercolation.LazyDFS.Exhaustive` and `OAI.CriticalPercolation.LazyDFS.GoodDarts` (definitions bundle `OAIQ228B002` of this split); `OAI.CriticalPercolation.BondGraph` (the published bundle `Def_CriticalPercolation`).
--
--   **Used by.** The proof of `OAI.CriticalPercolation.BinaryLaw.conditioned_inverse_cost` of this split imports it.
-- source:
--   OpenAI, No percolation at criticality on quasi-transitive graphs (result family 213), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 213; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/No-percolation-at-criticality-on-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/CriticalPercolation/Entropy/BinaryTranscript.lean (declaration OAI.CriticalPercolation.BinaryLaw.selected_moment)

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002

section

attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
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

variable {V E : Type*}

variable [Fintype V] [Fintype E]
variable (G : BondGraph V E) (order : List (LazyDFS.Dart V E)) (d : ℕ) (x : ℕ → V)
variable (p : ℝ) (w : E → Prop → ℝ) (n : ℕ) (D : FixedDescriptor n)

lemma selected_moment (horder : LazyDFS.GoodDarts G order) (ho : LazyDFS.Exhaustive G order)
    (hp : p ∈ Set.Ioo 0 1) (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p)
    (i : Fin n) (hi : i ∈ activeSteps n D) :
    (∑ ym : (E → Bool) × Option E,
      pushMass (selectedTranscript G d x n D i) (FiniteProduct.density (QueryTree.bitWeight p)) ym.1 *
      selectedWeight G order d x p w n D i ym.1 ym.2 *
        (1+selectedCost G order d x p w n D i ym.1 ym.2)) ≤ 4 := by
  sorry

end CriticalPercolation.BinaryLaw
end
end

end OAI
end
