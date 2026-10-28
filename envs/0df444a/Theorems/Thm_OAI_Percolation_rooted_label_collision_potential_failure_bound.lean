-- Prove2me | Theorems.Thm_OAI_Percolation_rooted_label_collision_potential_failure_bound
-- name    : OAI.Percolation.rooted_label_collision_potential_failure_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:52:20.978195+00:00
-- url     : https://prove2.me/theorems/51f781bb-cca9-4218-b9b1-730c1213b2ea
-- title:
--   OAI.Percolation.rooted_label_collision_potential_failure_bound: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.rooted_label_collision_potential_failure_bound` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/SelectionBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/SelectionBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem rooted_label_collision_potential_failure_bound [Countable V] [Countable E] [Nonempty V]
--       (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
--       {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
--       (htr : RootTransport root weight (vertexAut G))
--       (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
--       (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
--       (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
--       (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
--       (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
--       (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
--       (p : unitInterval) (hA : HasKernel G p A)
--       (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
--       (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
--       (hρ : ‖P‖ < 1) (J : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
--       (hsep : ∀ s ∈ segmentOrbit G γ,
--         (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
--         (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
--         2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep))
--       (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
--       (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
--       (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
--         if (labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
--           labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse) ∨
--           labelPotentialFailure G p γ ep neg L m F t ξ.1 then
--           escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
--         4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
--           2*(N*Real.sqrt c*‖P‖^m)/t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.EscapeLabel`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.PositiveRealMatrix`, `OAI.Percolation.RawFrom`, `OAI.Percolation.RootTransport`, `OAI.Percolation.matrixCoeff`, `OAI.Percolation.openSimpleGraph`, `OAI.Percolation.reachBall`, `OAI.Percolation.segmentOrbit`, `OAI.Percolation.vertexOrbit` and `OAI.Percolation.EscapeLabel.reverse` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.earlyCollisionCost` and `OAI.Percolation.suffixCollisionCost` (definitions bundle `OAIQ040C001` of this split); `OAI.Percolation.escapeLabelProbability`, `OAI.Percolation.labelFirstEscapeCollision`, `OAI.Percolation.labelPotentialFailure`, `OAI.Percolation.vertexAut` and `OAI.Percolation.walkKernel` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph`, `OAI.Percolation.HasKernel` and `OAI.Percolation.Hilbert` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.rooted_selected_label_mass_lower` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/SelectionBounds.lean (declaration OAI.Percolation.rooted_label_collision_potential_failure_bound)

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
universe u v w
variable {V : Type u} {E : Type v} {I : Type w}
section CombinedSelectionEvents
attribute [local instance] Classical.propDecidable Classical.decEq
variable [Fintype I]

theorem rooted_label_collision_potential_failure_bound [Countable V] [Countable E] [Nonempty V]
    (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    {ι : Type*} [Fintype ι] (root : ι → V) (weight : ι → ℝ)
    (htr : RootTransport root weight (vertexAut G))
    (hcov : ∀ x, ∃ r, ∃ g ∈ vertexAut G, g (root r) = x)
    (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (P A : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re)
    (p : unitInterval) (hA : HasKernel G p A)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n)
    (center ep neg : I) (L m : ℕ) (x : V) (hx : x ∈ vertexOrbit G (γ center))
    (hρ : ‖P‖ < 1) (J : ℕ) (posIdx negIdx suffixIdx : Fin (J+1) → I)
    (hsep : ∀ s ∈ segmentOrbit G γ,
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s (posIdx i))) ∧
      (∀ i, J ≤ (openSimpleGraph G Set.univ).dist (s ep) (s (negIdx i))) ∧
      2*J ≤ (openSimpleGraph G Set.univ).dist (s neg) (s ep))
    (F : (s : I → V) → RawFrom (openSimpleGraph G Set.univ) L (s ep) → (I → V) → Finset V)
    (N : ℝ) (hN : ∀ s mid h, ((F s mid h).card : ℝ) ≤ N) (t : ℝ) (ht : 0 < t) :
    (∑' ξ : {ξ : EscapeLabel G γ ep neg L m // ξ.first center = x},
      if (labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1 ∨
        labelFirstEscapeCollision G γ ep neg J L m posIdx negIdx suffixIdx ξ.1.reverse) ∨
        labelPotentialFailure G p γ ep neg L m F t ξ.1 then
        escapeLabelProbability G hloc a γ n hdiam center ep neg L m ξ.1 else 0) ≤
      4*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) +
        2*(N*Real.sqrt c*‖P‖^m)/t := by
  sorry

end CombinedSelectionEvents
end Percolation

end OAI
end
