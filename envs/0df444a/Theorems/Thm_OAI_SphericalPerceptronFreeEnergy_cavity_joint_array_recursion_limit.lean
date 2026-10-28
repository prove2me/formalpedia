-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_cavity_joint_array_recursion_limit
-- name    : OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:07:07.914973+00:00
-- url     : https://prove2.me/theorems/494b3f09-9d74-4365-bd88-6206865a5ab4
-- title:
--   OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit` of [lean/OAI/Probability/Perceptron/Cavity/CavityLabelLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityLabelLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology BigOperators BoundedContinuousFunction`):
--
--   ```lean
--   theorem cavity_joint_array_recursion_limit (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
--       (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
--       {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
--       (hbulk : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν))
--       (k : ℕ→ℕ) (p : (j : ℕ)→Fin (k j+1)→BulkPairRange K)
--       (D : ℕ→BulkPairRange K) (z : (j : ℕ)→Fin (k j)→ℝ)
--       (hp0 : ∀ j i,0 ≤ cavityPairProfile n d (p j) 0 i)
--       (hpm : ∀ j i,Monotone (fun l=>cavityPairProfile n d (p j) l i))
--       (hpD : ∀ j i,cavityPairProfile n d (p j) (Fin.last (k j)) i ≤ cavityPairDiagonal n d (D j) i)
--       (hz : ∀ j,StrictMono (z j)) (hz0 : ∀ j i,0<z j i) (hz1 : ∀ j i,z j i<1)
--       (hrpc : Tendsto (fun j=>cavityLabelMarkedLaw (p j) (D j) (z j)) atTop (𝓝 ν)) :
--       Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)) f (v (s j)) Λ hΛ-
--         ∫ y,finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
--           (gaussianLinearMarkStep (fun l=>diagonalMark (profileGaussianStep (cavityPairProfile n d (p j)) l))) (k j) (z j)
--           (fun t=>Real.log (cavityDiagonalAverage
--             (fun i=>Real.sqrt (cavityPairDiagonal n d (D j) i-cavityPairProfile n d (p j) (Fin.last (k j)) i))
--             (cavitySingleTest n d f.f Λ hΛ) (t 0)))
--           (fun _=>diagonalMark (profileGaussianRoot (cavityPairProfile n d (p j))) y)
--           ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.BulkPairRange`, `OAI.SphericalPerceptronFreeEnergy.CompactArray`, `OAI.SphericalPerceptronFreeEnergy.CompactOverlap`, `OAI.SphericalPerceptronFreeEnergy.Jet3`, `OAI.SphericalPerceptronFreeEnergy.bulkMarkedArrayLaw`, `OAI.SphericalPerceptronFreeEnergy.cavityBulkLog`, `OAI.SphericalPerceptronFreeEnergy.cavityDiagonalAverage`, `OAI.SphericalPerceptronFreeEnergy.cavityLabelMarkedLaw`, `OAI.SphericalPerceptronFreeEnergy.cavityPairDiagonal`, `OAI.SphericalPerceptronFreeEnergy.cavityPairProfile`, `OAI.SphericalPerceptronFreeEnergy.cavitySingleTest`, `OAI.SphericalPerceptronFreeEnergy.diagonalMark`, `OAI.SphericalPerceptronFreeEnergy.finiteCascadeLogRecursion`, `OAI.SphericalPerceptronFreeEnergy.gaussianLinearMarkStep`, `OAI.SphericalPerceptronFreeEnergy.gaussianMarkLaw`, `OAI.SphericalPerceptronFreeEnergy.profileGaussianRoot` and `OAI.SphericalPerceptronFreeEnergy.profileGaussianStep` (definitions bundle `OAIQ61Pf000` of this split).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.bulk_cavity_data` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Cavity/CavityLabelLimit.lean (declaration OAI.SphericalPerceptronFreeEnergy.cavity_joint_array_recursion_limit)

import Mathlib
import Definitions.Def_OAIQ61Pf000

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.markedTimePair_isProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators BoundedContinuousFunction

theorem cavity_joint_array_recursion_limit (n d : ℕ) (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    (Λ : ℝ) (hΛ : 1≤Λ) (K : ℝ) (hK : ∀ m,M m/(m+1:ℕ)*‖f.d1‖^2≤K) (s : ℕ→ℕ)
    {ν : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hbulk : Tendsto (fun j=>bulkMarkedArrayLaw (s j) (M (s j)) f (v (s j)) K (hK (s j))) atTop (𝓝 ν))
    (k : ℕ→ℕ) (p : (j : ℕ)→Fin (k j+1)→BulkPairRange K)
    (D : ℕ→BulkPairRange K) (z : (j : ℕ)→Fin (k j)→ℝ)
    (hp0 : ∀ j i,0 ≤ cavityPairProfile n d (p j) 0 i)
    (hpm : ∀ j i,Monotone (fun l=>cavityPairProfile n d (p j) l i))
    (hpD : ∀ j i,cavityPairProfile n d (p j) (Fin.last (k j)) i ≤ cavityPairDiagonal n d (D j) i)
    (hz : ∀ j,StrictMono (z j)) (hz0 : ∀ j i,0<z j i) (hz1 : ∀ j i,z j i<1)
    (hrpc : Tendsto (fun j=>cavityLabelMarkedLaw (p j) (D j) (z j)) atTop (𝓝 ν)) :
    Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)) f (v (s j)) Λ hΛ-
      ∫ y,finiteCascadeLogRecursion (gaussianMarkLaw (E:=EuclideanSpace ℝ (Fin (n+1)⊕Fin d)))
        (gaussianLinearMarkStep (fun l=>diagonalMark (profileGaussianStep (cavityPairProfile n d (p j)) l))) (k j) (z j)
        (fun t=>Real.log (cavityDiagonalAverage
          (fun i=>Real.sqrt (cavityPairDiagonal n d (D j) i-cavityPairProfile n d (p j) (Fin.last (k j)) i))
          (cavitySingleTest n d f.f Λ hΛ) (t 0)))
        (fun _=>diagonalMark (profileGaussianRoot (cavityPairProfile n d (p j))) y)
        ∂stdGaussian (EuclideanSpace ℝ (Fin (n+1)⊕Fin d))) atTop (𝓝 0) := by
  sorry

end SphericalPerceptronFreeEnergy
end

end OAI
end
