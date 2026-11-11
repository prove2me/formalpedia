-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_exists_cubic_bubble_separated_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:45:59.059247+00:00
-- url     : https://prove2.me/theorems/d8f9e936-125f-4834-8dc1-53338b275f4d
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated` of [lean/OAI/Geometry/BallPacking/BallMaps/CubicBubbleSeparated.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallMaps/CubicBubbleSeparated.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped ContDiff Manifold Topology BigOperators`, `open Set Function Manifold`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial`, `open MomentPolytope`):
--
--   ```lean
--    theorem exists_cubic_bubble_separated_bp240 {A B L S m p N k : ℕ}
--        (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
--        (hm : m+1<p) (t δ : ℝ) {c : ℝ} (hc : 0 < c)
--        {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0) (hDL : (L:ℝ)*D 0=1)
--        {r₀ : ℝ} (hr₀ : r₀<Real.pi*(D 0*((m+1:ℕ)*c)))
--        (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
--        (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
--          (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ) (f i))
--        (hinto : ∀ i,∀ x∈closedBall 3 (r i),(f i x).2≠0)
--        (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j))))
--        {η : ℝ} (hη : 0<η) :
--        ∃ ε∈Ioc (0:ℝ) η,∃ g₀ : Ambient 3 → Ambient 3,∃ g : Fin k → Ambient 3 → Ambient 3,
--          FormNeighborhoodEmbedding (closedBall 3 r₀) (fun _ => successorStandardForm 2)
--            (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) g₀ ∧
--          (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
--            (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) (g i)) ∧
--          (∀ i,Disjoint (g₀ '' closedBall 3 r₀) (g i '' closedBall 3 (r i))) ∧
--          Pairwise (fun i j => Disjoint (g i '' closedBall 3 (r i)) (g j '' closedBall 3 (r j)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.Ambient`, `OAI.PackingSufficiencySupport.CubicModel.CubicAmbient`, `OAI.PackingSufficiencySupport.CubicModel.PlaneBase`, `OAI.PackingSufficiencySupport.CubicModel.WeightedAffineIndex`, `OAI.PackingSufficiencySupport.CubicModel.WeightedHomogeneousIndex`, `OAI.PackingSufficiencySupport.CubicModel.cubicBubblePolynomial`, `OAI.PackingSufficiencySupport.FiniteMoment.TrapezoidWeight` and `OAI.PackingSufficiencySupport.Hamiltonian.FormNeighborhoodEmbedding` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.closedBall` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.CubicModel.outerAmbientForm` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.degreeAffineForm` and `OAI.PackingSufficiencySupport.Hamiltonian.successorStandardForm` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.CubicModel.cubic_bubble_target_packing_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/BallMaps/CubicBubbleSeparated.lean (declaration OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial
open MomentPolytope

 theorem exists_cubic_bubble_separated_bp240 {A B L S m p N k : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1<p) (t δ : ℝ) {c : ℝ} (hc : 0 < c)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0) (hDL : (L:ℝ)*D 0=1)
     {r₀ : ℝ} (hr₀ : r₀<Real.pi*(D 0*((m+1:ℕ)*c)))
     (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
     (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ) (f i))
     (hinto : ∀ i,∀ x∈closedBall 3 (r i),(f i x).2≠0)
     (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j))))
     {η : ℝ} (hη : 0<η) :
     ∃ ε∈Ioc (0:ℝ) η,∃ g₀ : Ambient 3 → Ambient 3,∃ g : Fin k → Ambient 3 → Ambient 3,
       FormNeighborhoodEmbedding (closedBall 3 r₀) (fun _ => successorStandardForm 2)
         (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) g₀ ∧
       (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
         (degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)) (g i)) ∧
       (∀ i,Disjoint (g₀ '' closedBall 3 r₀) (g i '' closedBall 3 (r i))) ∧
       Pairwise (fun i j => Disjoint (g i '' closedBall 3 (r i)) (g j '' closedBall 3 (r j))) := by
  sorry

end PackingSufficiencySupport.CubicModel

end

end OAI
end
