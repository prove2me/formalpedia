-- Prove2me | Theorems.Thm_OAI_Mahler_MassHypotheses_homogeneousResidualFlux_eq_zero_of_transgression_eq
-- name    : OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T01:21:42.063571+00:00
-- url     : https://prove2.me/theorems/47ef769b-d010-40d3-9497-2e022ea3aab0
-- title:
--   OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression_eq: intermediate lemma from OpenAI, The symmetric Mahler conjecture and its equality cases
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SymmetricMahler.symmetric_mahler_equality`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The symmetric Mahler conjecture and its equality cases*, OpenAI Math Release, September 22, 2026, result family 87, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression` of [lean/OAI/Analysis/Mahler/Mahler/HomogeneousTransgressionFTC.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/HomogeneousTransgressionFTC.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Mahler`, with `open Complex Set Metric`, `open scoped Topology`):
--
--   ```lean
--   theorem MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression_eq {k N m : ℕ}
--       {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
--       {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
--       (t : ℝ)
--       (ht : ∀ x : ComplexEuclidean (k+2), ‖x‖ = 1 →
--         ∀ v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2),
--         (∀ i, inner ℝ x (v i) = 0) →
--         boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
--           (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
--           -((k+1 : ℕ) : ℂ) * extDeriv (sourceHomogeneousPrimitive (m := m) G t) x v) :
--       sphereFlux (k+1) (boundaryResidualFin
--         (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
--         (betaLinear (polynomialMap G) (coordinateMap (k+2)) m)) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Mahler.ComplexEuclidean`, `OAI.Mahler.MassHypotheses`, `OAI.Mahler.alphaPath`, `OAI.Mahler.betaLinear`, `OAI.Mahler.boundaryResidualFin`, `OAI.Mahler.coordinateMap`, `OAI.Mahler.polynomialMap`, `OAI.Mahler.sourceHomogeneousPrimitive` and `OAI.Mahler.sphereFlux` (definitions bundle `OAIQ2Ma000` of this split).
--
--   **Used by.** The proof of `OAI.Mahler.MassHypotheses.homogeneousFlux_endpoints_of_transgression_eq` of this split imports it.
-- source:
--   OpenAI, The symmetric Mahler conjecture and its equality cases, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 87; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-symmetric-Mahler-conjecture-and-its-equality-cases-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Mahler/Mahler/HomogeneousTransgressionFTC.lean (declaration OAI.Mahler.MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression)

import Mathlib
import Definitions.Def_OAIQ2Ma000

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex Set Metric
open scoped Topology

noncomputable section
namespace Mahler

theorem MassHypotheses.homogeneousResidualFlux_eq_zero_of_transgression_eq {k N m : ℕ}
    {U : Set (ComplexEuclidean (k+2))} {f : Fin N → ComplexEuclidean (k+2) → ℂ}
    {G : Fin N → MvPolynomial (Fin (k+2)) ℂ} (h : MassHypotheses (k+2) N m U f G)
    (t : ℝ)
    (ht : ∀ x : ComplexEuclidean (k+2), ‖x‖ = 1 →
      ∀ v : Fin (2*(k+1)+1) → ComplexEuclidean (k+2),
      (∀ i, inner ℝ x (v i) = 0) →
      boundaryResidualFin (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
        (betaLinear (polynomialMap G) (coordinateMap (k+2)) m) x v =
        -((k+1 : ℕ) : ℂ) * extDeriv (sourceHomogeneousPrimitive (m := m) G t) x v) :
    sphereFlux (k+1) (boundaryResidualFin
      (alphaPath (polynomialMap G) (coordinateMap (k+2)) m t)
      (betaLinear (polynomialMap G) (coordinateMap (k+2)) m)) = 0 := by
  sorry

end Mahler

end

end OAI
end
