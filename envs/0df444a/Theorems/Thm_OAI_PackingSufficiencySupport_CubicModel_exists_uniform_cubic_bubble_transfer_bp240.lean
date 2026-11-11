-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_exists_uniform_cubic_bubble_transfer_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:48:09.038846+00:00
-- url     : https://prove2.me/theorems/ac4d178a-a0fe-4e90-b467-5366076274ae
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer` of [lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped ContDiff Manifold`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial`, `open scoped Topology`, `open Set Function Manifold`):
--
--   ```lean
--    theorem exists_uniform_cubic_bubble_transfer_bp240 {L S A B p N : ℕ} (m : ℕ)
--        (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
--        (hm : m+1≤p) (t δ : ℝ) {c : ℝ} (hc : 0 < c)
--        {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0)
--        {K : Set (Fin 3 → ℂ)} (hK : IsCompact K)
--        {T : Set (Fin 3 → ℂ)} (hT : IsOpen T) (h0T : (0 : Fin 3 → ℂ)∈T)
--        {η : ℝ} (hη : 0<η) :
--        ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : (Fin 3 → ℂ) → (Fin 3 → ℂ),∃ W,
--          IsOpen W ∧ K⊆W ∧ ContDiff ℝ ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
--          MapsTo g W T ∧ ∀ x∈W,∀ v w,
--            degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)
--              (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
--            D 0*affineFSForm ((m+1:ℕ)*c) (complexCartesian x) (complexCartesian v) (complexCartesian w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.CubicModel.WeightedAffineIndex`, `OAI.PackingSufficiencySupport.CubicModel.WeightedHomogeneousIndex`, `OAI.PackingSufficiencySupport.CubicModel.cubicBubblePolynomial`, `OAI.PackingSufficiencySupport.FiniteMoment.TrapezoidWeight`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase` and `OAI.PackingSufficiencySupport.Hamiltonian.affineFSForm` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.complexCartesian` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.degreeAffineForm` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.CubicModel.exists_cubic_bubble_separated_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CompactUniformCentral.lean (declaration OAI.PackingSufficiencySupport.CubicModel.exists_uniform_cubic_bubble_transfer)

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
open scoped ContDiff Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial
open scoped Topology
open Set Function Manifold

 theorem exists_uniform_cubic_bubble_transfer_bp240 {L S A B p N : ℕ} (m : ℕ)
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hp : p<L-S) (hN : p<N)
     (hm : m+1≤p) (t δ : ℝ) {c : ℝ} (hc : 0 < c)
     {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0<D 0)
     {K : Set (Fin 3 → ℂ)} (hK : IsCompact K)
     {T : Set (Fin 3 → ℂ)} (hT : IsOpen T) (h0T : (0 : Fin 3 → ℂ)∈T)
     {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : (Fin 3 → ℂ) → (Fin 3 → ℂ),∃ W,
       IsOpen W ∧ K⊆W ∧ ContDiff ℝ ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
       MapsTo g W T ∧ ∀ x∈W,∀ v w,
         degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m+1) p N t δ ε) c (D ε)
           (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
         D 0*affineFSForm ((m+1:ℕ)*c) (complexCartesian x) (complexCartesian v) (complexCartesian w) := by
  sorry

end PackingSufficiencySupport.CubicModel

end

end OAI
end
