-- Prove2me | Theorems.Thm_OAI_TamingCompatibility_GeometricHilbert_FirstJetGauge_actualSquareFirst_skew
-- name    : OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:11:40.096872+00:00
-- url     : https://prove2.me/theorems/601b21d1-356f-4ac2-bbac-bad77f3c8aab
-- title:
--   OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew: intermediate lemma from OpenAI, Taming implies compatibility on four-manifolds
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.TamingCompatibility.taming_implies_compatibility`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Taming implies compatibility on four-manifolds*, OpenAI Math Release, October 6, 2026, result family 342, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew` of [lean/OAI/Geometry/TamingCompatibility/Elliptic/WeightedPrincipal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Elliptic/WeightedPrincipal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge`, with `open Filter`, `open scoped ContDiff Topology`):
--
--   ```lean
--   lemma actualSquareFirst_skew (e : ι → V) (a : ι → V → W →L[ℝ] Q)
--       (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (g : ι → ι → V → ℝ) (x : V)
--       (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hρ : DifferentiableAt ℝ ρ x)
--       (hg : ∀ i j, DifferentiableAt ℝ (g i j) x)
--       (hscalar : ∀ i j, (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z)
--         =ᶠ[𝓝 x] (fun z => (2*(ρ z*g i j z)) • ContinuousLinearMap.id ℝ W))
--       (hρ0 : fderiv ℝ ρ x = 0) (hg0 : ∀ i j, fderiv ℝ (g i j) x = 0) (j : ι) :
--       (actualSquareFirst e a b ρ j x).adjoint = -actualSquareFirst e a b ρ j x
--   ```
--
--   **Definitions.** The statement is written with `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.End`, `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst` and `OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.weightedPrincipal` (definitions bundle `OAIQ239Tc003` of this split).
--
--   **Used by.** The proof of `OAI.TamingCompatibility.GeometricHilbert.GeometricNormalCharts.ActualData.jets` of this split imports it.
-- source:
--   OpenAI, Taming implies compatibility on four-manifolds, OpenAI Math Release, October 6, 2026, https://github.com/openai/math (result family 342; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Taming-implies-compatibility-on-four-manifolds-October-6-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/TamingCompatibility/Elliptic/WeightedPrincipal.lean (declaration OAI.TamingCompatibility.GeometricHilbert.FirstJetGauge.actualSquareFirst_skew)

import Mathlib
import Definitions.Def_OAIQ239Tc003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace TamingCompatibility.GeometricHilbert.FirstJetGauge
open Filter
open scoped ContDiff Topology
variable {V W Q ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
  [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
attribute [local instance] ContinuousLinearMap.toNormedAddCommGroup ContinuousLinearMap.toNormedSpace

variable [Fintype ι]

lemma actualSquareFirst_skew (e : ι → V) (a : ι → V → W →L[ℝ] Q)
    (b : V → W →L[ℝ] Q) (ρ : V → ℝ) (g : ι → ι → V → ℝ) (x : V)
    (ha : ∀ i, DifferentiableAt ℝ (a i) x) (hρ : DifferentiableAt ℝ ρ x)
    (hg : ∀ i j, DifferentiableAt ℝ (g i j) x)
    (hscalar : ∀ i j, (fun z => weightedPrincipal a ρ i j z + weightedPrincipal a ρ j i z)
      =ᶠ[𝓝 x] (fun z => (2*(ρ z*g i j z)) • ContinuousLinearMap.id ℝ W))
    (hρ0 : fderiv ℝ ρ x = 0) (hg0 : ∀ i j, fderiv ℝ (g i j) x = 0) (j : ι) :
    (actualSquareFirst e a b ρ j x).adjoint = -actualSquareFirst e a b ρ j x := by
  sorry

end TamingCompatibility.GeometricHilbert.FirstJetGauge

end

end OAI
end
