-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_constructed_surface_collar_family
-- name    : OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T09:46:35.157438+00:00
-- url     : https://prove2.me/theorems/ea078354-edfb-4096-9cec-aa620bd00b47
-- title:
--   OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family` of [lean/OAI/Geometry/SurfaceImmersion/Whitney/ConstructedCollarFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/ConstructedCollarFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.SurfaceVelocityFamily`, with `open Set`, `open scoped ContDiff Matrix`, `open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates`, `open VelocityFrame NormalFrame TransverseSmallFunction`):
--
--   ```lean
--   theorem constructed_surface_collar_family {F : RField 4} (hF : ContDiff ℝ ∞ F)
--       {C₀ L U Ω : Set CollarVelocity.JetBase}
--       (hC₀ : IsCompact C₀) (hL : IsCompact L) (hCL : C₀ ⊆ L)
--       (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C₀ ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
--       {e₁ e₂ : CollarVelocity.JetBase → Vec} {a : CollarVelocity.JetBase → ℝ}
--       (he₁ : ContDiffOn ℝ ∞ e₁ Ω) (he₂ : ContDiffOn ℝ ∞ e₂ Ω)
--       (ha : ContDiffOn ℝ ∞ a Ω) (hD : ∀ j ∈ Ω, gramDet (j.2 1) (j.2 4) ≠ 0)
--       (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
--         j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
--       (hcollar : ∀ j ∈ U, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j))
--       (hn : ∀ j ∈ Ω, jetNormal j ≠ 0 ∨ a j ≠ 0)
--       (hap : ∀ j ∈ L \ C₀, 0 < a j) (haC : ∀ j ∈ C₀, a j = 0) :
--       ∃ W : Set CollarVelocity.JetBase, IsOpen W ∧ C₀ ⊆ W ∧ W ⊆ U ∧
--         ∀ ε : ℝ, 0 < ε → ∃ V : Set CollarVelocity.JetBase, IsOpen V ∧ C₀ ⊆ V ∧ V ⊆ W ∧
--         ∀ (K O P : Set SmallModes.Base), IsCompact K → MapsTo (CollarVelocity.jetSection F) K L →
--           IsOpen O → K ⊆ O → (∀ j ∈ C₀, j.1 ∉ closure O) → P.Finite → P ⊆ K →
--           (∀ p ∈ K \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
--             ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
--               fderiv ℝ f p (0,1) ≠ 0) →
--         ∀ T : ℝ, ∃ Z : TopologicalSpace.Opens CollarVelocity.JetBase,
--           L ⊆ Z ∧ (Z : Set CollarVelocity.JetBase) ⊆ Ω ∧
--           ∃ l : Loop (jetDomain Z), (∀ J, l.amplitude J = a (decode J)) ∧
--             (∃ W' : Set CollarVelocity.JetBase, IsOpen W' ∧ C₀ ⊆ W' ∧ W' ⊆ W ∧
--               ∀ J, decode J ∈ W' → a (decode J) = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
--             ∃ α : CollarVelocity.JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
--               (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
--               (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J)) •
--                 direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
--               (∀ j ∈ V, ∀ t, |α (j,t)| < ε) ∧
--               ∃ τ : SmallModes.Base → ℝ,
--                 (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
--                   deriv (fun t => α (CollarVelocity.jetSection F x,t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
--                 ∀ x ∈ K, T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,0)) x (0,1) ∧
--                   T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,τ x)) x (0,1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet` and `OAI.ClosedSurfaceR4.TransverseSmallFunction.Base` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.CollarVelocity.JetBase`, `OAI.ClosedSurfaceR4.CollarVelocity.jetSection`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.RealTwoJet`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.normal` and `OAI.ClosedSurfaceR4.VelocityFrame.normalize` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.VelocityFrame.velocityRadius` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.VelocityFrame.direction` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.SurfaceJetCoordinates.decode`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetDomain` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.jetNormal` (definitions bundle `OAIQ249SI009` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.actual_surface_collar_profile_family` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Whitney/ConstructedCollarFamily.lean (declaration OAI.ClosedSurfaceR4.SurfaceVelocityFamily.constructed_surface_collar_family)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Definitions.Def_OAIQ249SI009

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates SurfaceJetCoordinates
open VelocityFrame NormalFrame TransverseSmallFunction

theorem constructed_surface_collar_family {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {C₀ L U Ω : Set CollarVelocity.JetBase}
    (hC₀ : IsCompact C₀) (hL : IsCompact L) (hCL : C₀ ⊆ L)
    (hU : IsOpen U) (hΩ : IsOpen Ω) (hCU : C₀ ⊆ U) (hUΩ : U ⊆ Ω) (hLΩ : L ⊆ Ω)
    {e₁ e₂ : CollarVelocity.JetBase → Vec} {a : CollarVelocity.JetBase → ℝ}
    (he₁ : ContDiffOn ℝ ∞ e₁ Ω) (he₂ : ContDiffOn ℝ ∞ e₂ Ω)
    (ha : ContDiffOn ℝ ∞ a Ω) (hD : ∀ j ∈ Ω, gramDet (j.2 1) (j.2 4) ≠ 0)
    (hframe : ∀ j ∈ Ω, e₁ j ⬝ᵥ e₁ j = 1 ∧ e₂ j ⬝ᵥ e₂ j = 1 ∧ e₁ j ⬝ᵥ e₂ j = 0 ∧
      j.2 1 ⬝ᵥ e₁ j = 0 ∧ j.2 4 ⬝ᵥ e₁ j = 0 ∧ j.2 1 ⬝ᵥ e₂ j = 0 ∧ j.2 4 ⬝ᵥ e₂ j = 0)
    (hcollar : ∀ j ∈ U, jetNormal j ≠ 0 ∧ e₁ j = normalize (jetNormal j))
    (hn : ∀ j ∈ Ω, jetNormal j ≠ 0 ∨ a j ≠ 0)
    (hap : ∀ j ∈ L \ C₀, 0 < a j) (haC : ∀ j ∈ C₀, a j = 0) :
    ∃ W : Set CollarVelocity.JetBase, IsOpen W ∧ C₀ ⊆ W ∧ W ⊆ U ∧
      ∀ ε : ℝ, 0 < ε → ∃ V : Set CollarVelocity.JetBase, IsOpen V ∧ C₀ ⊆ V ∧ V ⊆ W ∧
      ∀ (K O P : Set SmallModes.Base), IsCompact K → MapsTo (CollarVelocity.jetSection F) K L →
        IsOpen O → K ⊆ O → (∀ j ∈ C₀, j.1 ∉ closure O) → P.Finite → P ⊆ K →
        (∀ p ∈ K \ P, ∃ N : Set SmallModes.Base, IsOpen N ∧ p ∈ N ∧
          ∃ f : SmallModes.Base → ℝ, ContDiffOn ℝ ∞ f N ∧ (∀ x ∈ K ∩ N, f x = 0) ∧
            fderiv ℝ f p (0,1) ≠ 0) →
      ∀ T : ℝ, ∃ Z : TopologicalSpace.Opens CollarVelocity.JetBase,
        L ⊆ Z ∧ (Z : Set CollarVelocity.JetBase) ⊆ Ω ∧
        ∃ l : Loop (jetDomain Z), (∀ J, l.amplitude J = a (decode J)) ∧
          (∃ W' : Set CollarVelocity.JetBase, IsOpen W' ∧ C₀ ⊆ W' ∧ W' ⊆ W ∧
            ∀ J, decode J ∈ W' → a (decode J) = 0 → ∀ t, l.velocity (J,t) = normal J) ∧
          ∃ α : CollarVelocity.JetBase × ℝ → ℝ, ContDiffOn ℝ ∞ α (Z ×ˢ univ) ∧
            (∀ j ∈ Z, Function.Periodic (fun t => α (j,t)) 1) ∧
            (∀ J t, l.velocity (J,t) = velocityRadius (normal J) (a (decode J)) •
              direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t))) ∧
            (∀ j ∈ V, ∀ t, |α (j,t)| < ε) ∧
            ∃ τ : SmallModes.Base → ℝ,
              (∀ x ∈ K, ∀ θ ∈ Ico (0 : ℝ) 1,
                deriv (fun t => α (CollarVelocity.jetSection F x,t)) θ = 0 ↔ θ = 0 ∨ θ = τ x) ∧
              ∀ x ∈ K, T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,0)) x (0,1) ∧
                T < fderiv ℝ (fun y => α (CollarVelocity.jetSection F y,τ x)) x (0,1) := by
  sorry

end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end
