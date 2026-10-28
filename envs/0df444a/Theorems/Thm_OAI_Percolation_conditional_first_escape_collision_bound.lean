-- Prove2me | Theorems.Thm_OAI_Percolation_conditional_first_escape_collision_bound
-- name    : OAI.Percolation.conditional_first_escape_collision_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T00:48:38.003986+00:00
-- url     : https://prove2.me/theorems/ed9c26b3-f058-4bb6-91e6-9ec4678c36b3
-- title:
--   OAI.Percolation.conditional_first_escape_collision_bound: intermediate lemma from OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Percolation.arbitrary_cayley`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214)*, OpenAI Math Release, September 24, 2026, result family 214, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Percolation.conditional_first_escape_collision_bound` of [lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PositiveEscapes.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PositiveEscapes.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Percolation`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`):
--
--   ```lean
--   theorem conditional_first_escape_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
--       (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
--       (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
--       (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
--       (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
--       (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
--       (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
--       (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
--       (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
--       (m L J : ℕ) (x y : V) (hy : y ∈ vertexOrbit G (γ ep))
--       (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
--       (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
--       (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
--       (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
--       (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
--         ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
--           ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
--             if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
--               tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
--                 (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
--           segmentReturnMass G hloc a γ ep L y ≤
--         2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Percolation.HoldingWalk`, `OAI.Percolation.LocallyFinite`, `OAI.Percolation.PositiveRealMatrix`, `OAI.Percolation.RawFrom`, `OAI.Percolation.RootTransport`, `OAI.Percolation.matrixCoeff`, `OAI.Percolation.openSimpleGraph`, `OAI.Percolation.reachBall`, `OAI.Percolation.segmentAnchors`, `OAI.Percolation.vertexOrbit` and `OAI.Percolation.HoldingWalk.mass` (definitions bundle `OAIQ040C000` of this split); `OAI.Percolation.earlyCollisionCost` and `OAI.Percolation.suffixCollisionCost` (definitions bundle `OAIQ040C001` of this split); `OAI.Percolation.firstEscapeCollision`, `OAI.Percolation.segmentReturnMass`, `OAI.Percolation.vertexAut` and `OAI.Percolation.walkKernel` (definitions bundle `OAIQ040C002` of this split); `OAI.Percolation.BondGraph` and `OAI.Percolation.Hilbert` (the published bundle `Def_CayleyPercolation`).
--
--   **Used by.** The proof of `OAI.Percolation.rooted_label_collision_potential_failure_bound` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness of percolation on nonamenable quasi-transitive graphs (result family 214), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 214; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-of-percolation-on-nonamenable-quasi-transitive-graphs-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/UnimodularPercolation/UnimodularPercolation/Escape/PositiveEscapes.lean (declaration OAI.Percolation.conditional_first_escape_collision_bound)

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
section NormalizedFirstEscape
attribute [local instance] Classical.propDecidable Classical.decEq
variable {I ι : Type*} [Fintype I] [Fintype ι]

theorem conditional_first_escape_collision_bound (G : BondGraph V E) (hloc : LocallyFinite G) (a : ℝ)
    (root : ι → V) (weight : ι → ℝ) (Γ : Set (V ≃ V)) (hΓ : Γ ⊆ vertexAut G)
    (htr : RootTransport root weight Γ) (hw : ∀ r, 0 < weight r) (hw1 : ∑ r, weight r = 1)
    (hcov : ∀ x, ∃ r, ∃ g ∈ Γ, g (root r) = x)
    (c : ℝ) (hc : 0 < c) (hmin : ∀ r, 1 ≤ c*weight r)
    (γ : I → V) (n : ℕ) (hdiam : ∀ i j, γ j ∈ reachBall G (γ i) n) (ep : I)
    (P : Hilbert V →L[ℂ] Hilbert V) (hpos : PositiveRealMatrix P) (hsym : IsSelfAdjoint P)
    (hP : ∀ x y, matrixCoeff P x y = (walkKernel G hloc a x y : ℂ))
    (hdiag : ∀ x, 1/2 ≤ (matrixCoeff P x x).re) (hρ : ‖P‖ < 1)
    (m L J : ℕ) (x y : V) (hy : y ∈ vertexOrbit G (γ ep))
    (pos neg : Fin (J+1) → V) (j : Fin (J+1) → I)
    (hposD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist x (pos s))
    (hnegD : ∀ s, J ≤ (openSimpleGraph G Set.univ).dist y (neg s))
    (hxy : 2*J ≤ (openSimpleGraph G Set.univ).dist x y) :
    (∑' tail : RawFrom (openSimpleGraph G Set.univ) m x,
      ∑' mid : RawFrom (openSimpleGraph G Set.univ) L y,
        ∑' h : segmentAnchors G hloc γ n hdiam ep mid.1,
          if firstEscapeCollision G J m L x y pos neg j tail mid h.val then
            tail.2.mass (walkKernel G hloc a)*mid.2.mass (walkKernel G hloc a)/
              (segmentAnchors G hloc γ n hdiam ep (γ ep)).card else 0) /
        segmentReturnMass G hloc a γ ep L y ≤
      2*c*(earlyCollisionCost ‖P‖ J + suffixCollisionCost ‖P‖ c J*‖P‖^L) := by
  sorry

end NormalizedFirstEscape
end Percolation

end OAI
end
