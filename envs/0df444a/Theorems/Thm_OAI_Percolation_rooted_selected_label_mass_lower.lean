-- Prove2me | Theorems.Thm_OAI_Percolation_rooted_selected_label_mass_lower
-- name    : OAI.Percolation.rooted_selected_label_mass_lower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:52:45.062061+00:00
-- url     : https://prove2.me/theorems/7479f85d-8aff-4c1f-a077-ea7b6c85e027
-- title:
--   OAI.Percolation.rooted_selected_label_mass_lower: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.rooted_selected_label_mass_lower` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PathSelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PathSelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem rooted_selected_label_mass_lower [Countable V] [Countable E] [Nonempty V]
--       (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
--       (root : ι → V) (weight : ι → ℝ)
--       (htr : RootTransport root weight (vertexAut G))
--       (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
--       (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
--       (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
--       (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
--       (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
--       (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
--       (p : unitInterval) (hA : HasKernel G p A)
--       (J L m : ℕ) (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
--       (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
--       (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) (J+J))
--       (x : V) (hx : x ∈ vertexOrbit G (γ (segmentCenter J))) (hρ : ‖P‖ < 1)
--       (hsep : ∀ s ∈ segmentOrbit G γ,
--         (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (segmentPositiveIndex J i))) ∧
--         (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s (Fin.last (J+J))) (s (segmentNegativeIndex J i))) ∧
--         2*J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (Fin.last (J+J))))
--       (d : ℕ) (hd : ∀ z, degree G z ≤ d) (t : ℝ) (ht : 0 < t) :
--       1 - (4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
--         2*((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)*Real.sqrt c*‖P‖^m)/t +
--         2*c*(((d+1)^2:ℕ):ℝ)*Real.sqrt c*‖P‖^L) ≤
--       ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
--         if (labelCorridor G J L m γ hγ ξ.1).Selected hloc p (J+m) t then
--           escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.EscapeLabel`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.PositiveRealMatrix`, `OAI.Percolation.RootTransport`, `OAI.Percolation.matrixCoeff`, `OAI.Percolation.openSimpleGraph`, `OAI.Percolation.reachBall`, `OAI.Percolation.segmentOrbit`, `OAI.Percolation.vertexOrbit` and `OAI.Percolation.RawCorridor.Selected` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.earlyCollisionCost`, `OAI.Percolation.segmentCenter`, `OAI.Percolation.segmentNegativeIndex`, `OAI.Percolation.segmentPositiveIndex` and `OAI.Percolation.suffixCollisionCost` (definitions bundle `OAIQ040C001` of this split); `OAI.Percolation.degree`, `OAI.Percolation.escapeLabelProbability`, `OAI.Percolation.labelCorridor`, `OAI.Percolation.vertexAut` and `OAI.Percolation.walkKernel` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.HasKernel` and `OAI.Percolation.Hilbert` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.exists_selected_path_mass` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PathSelection.lean (declaration OAI.Percolation.rooted_selected_label_mass_lower)

import Mathlib
import Definitions.Def_CayleyPercolation
import Definitions.Def_OAIQ040C002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace Percolation
universe u v
variable {V : Type u} {E : Type v}
section SelectedLabelMass
attribute [local instance] Classical.propDecidable Classical.decEq
variable {ι : Type*} [Fintype ι]

theorem rooted_selected_label_mass_lower [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (J L m : ℕ) (γ : Fin (J+J+1) → V) (hinj : Function.Injective γ)
    (hγ : ∀ i : Fin (J+J), (openSimpleGraph G Set.univ).Adj (γ i.castSucc) (γ i.succ))
    (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) (J+J))
    (x : V) (hx : x ∈ vertexOrbit G (γ (segmentCenter J))) (hρ : ‖P‖ < 1)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (segmentPositiveIndex J i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s (Fin.last (J+J))) (s (segmentNegativeIndex J i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s 0) (s (Fin.last (J+J))))
    (d : ℕ) (hd : ∀ z, degree G z ≤ d) (t : ℝ) (ht : 0 < t) :
    1 - (4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
      2*((3*(d:ℝ)+3)*((((J+L)+J):ℕ)+1)*Real.sqrt c*‖P‖^m)/t +
      2*c*(((d+1)^2:ℕ):ℝ)*Real.sqrt c*‖P‖^L) ≤
    ∑' ξ : {ξ : EscapeLabel G γ (Fin.last (J+J)) 0 L m // ξ.first (segmentCenter J) = x},
      if (labelCorridor G J L m γ hγ ξ.1).Selected hloc p (J+m) t then
        escapeLabelProbability G hloc a γ (J+J) hdiam (segmentCenter J) (Fin.last (J+J)) 0 L m ξ.1 else 0 := by
  sorry

end SelectedLabelMass
end Percolation

end OAI
end
