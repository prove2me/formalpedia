-- Prove2me | Theorems.Thm_OAI_SmoothObstruction_EuclideanSplitting_endpoint_bounds
-- name    : OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:16:35.865156+00:00
-- url     : https://prove2.me/theorems/7f5e147e-bb55-4e53-b099-4041ab95ef18
-- title:
--   OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds: intermediate lemma from OpenAI, Zero entropy does not guarantee a smooth positive-volume model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SmoothObstruction.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Zero entropy does not guarantee a smooth positive-volume model*, OpenAI Math Release, September 25, 2026, result family 152, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds` of [lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/EndpointFrames.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/EndpointFrames.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SmoothObstruction.EuclideanSplitting`, with `open Filter Topology`, `open scoped Real`, `open Set Matrix ExteriorStability`, `open scoped Matrix.Norms.L2Operator`):
--
--   ```lean
--   theorem endpoint_bounds
--       (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
--       (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
--       (S : Finset (Fin d)) (hSp : S.card=p) (n : ℕ) {γ g K C δ : ℝ}
--       (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
--       (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
--       (hUs : ‖U 0‖≤Real.exp K) (hUt : ‖U n‖≤Real.exp K)
--       (hVs : ‖V 0‖≤Real.exp K) (hVt : ‖V n‖≤Real.exp K)
--       (hpoly : ∀ A : E₀ →L[ℝ] E₀,‖exterior p A‖≤C*(max 1 ‖A‖)^p)
--       (W G Gslow : Submodule ℝ E₀) (hdim : Module.finrank ℝ W=p)
--       (hend : ‖(groupSpace (U n) (V n) (hUV n) (hVU n) S).starProjection-W.starProjection‖≤1/2)
--       (hstart : ‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) S).starProjection-G.starProjection‖≤δ)
--       (hstartSlow : ‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) Sᶜ).starProjection-Gslow.starProjection‖≤δ)
--       (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
--       (hr : ∀ j∈r,b j∈W) (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
--       (v : Fin p → E₀) (horth : Orthonormal ℝ v) (hv : ∀ i,v i∈G)
--       (z : Fin q → E₀) (hz : ∀ j,z j∈Gslow) (hznorm : ∀ j,‖z j‖≤1)
--       (hsmall : (frameWedgeConstant (E := E₀) p*δ)*
--         (1+((C*(Real.exp K)^p)^2*(C*2^p))*
--           (C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p):ℝ))))≤1/2)
--       (B : E₀ →L[ℝ] E₀) {ζ : ℝ} (hζ : 0≤ζ)
--       (hpert : 2*((C*(Real.exp K)^p)^2*(C*2^p))*C*ζ*‖continuousWedge (E := E₀) p‖<1)
--       (hdiff : ‖exterior p B-
--         exterior p (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (transition U V lam 0 n))‖≤
--           ζ*Real.exp ((n:ℝ)*(∑ j∈S,lam j))) :
--       let A₀ := endpointMatrix b p r
--         (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (transition U V lam 0 n)) v
--       let A := endpointMatrix b p r B v
--       let H := endpointMatrix b p r B z
--       let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
--       let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p):ℝ))
--       let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p):ℝ)*‖continuousWedge (E := E₀) p‖
--       let θ := 2*L₀*(N₁*Real.exp (-2*g*n)+N₀*unitWedgeConstant (E := E₀) p*δ)
--       let ε := 2*L₀*C*ζ*‖continuousWedge (E := E₀) p‖
--       A₀.det≠0 ∧ A.det≠0 ∧ |A.det/A₀.det-1|≤ε ∧ ∀ i j,|(A⁻¹*H) i j|≤(θ+ε)/(1-ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SmoothObstruction.EuclideanSplitting.groupSpace`, `OAI.SmoothObstruction.EuclideanSplitting.transition`, `OAI.SmoothObstruction.ExteriorStability.continuousWedge`, `OAI.SmoothObstruction.ExteriorStability.endpointMatrix`, `OAI.SmoothObstruction.ExteriorStability.exterior`, `OAI.SmoothObstruction.ExteriorStability.frameWedgeConstant` and `OAI.SmoothObstruction.ExteriorStability.unitWedgeConstant` (definitions bundle `OAIQ5T3000` of this split).
--
--   **Used by.** The proof of `OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp` of this split imports it.
-- source:
--   OpenAI, Zero entropy does not guarantee a smooth positive-volume model, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 152; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/EndpointFrames.lean (declaration OAI.SmoothObstruction.EuclideanSplitting.endpoint_bounds)

import Mathlib
import Definitions.Def_OAIQ5T3000

section

attribute [-instance] _root_.OAI.SmoothObstruction.PairUpper.nonzeroNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Filter Topology
open scoped Real

namespace SmoothObstruction.EuclideanSplitting
open Set Matrix ExteriorStability
open scoped Matrix.Norms.L2Operator
variable {d p q : ℕ}
local notation "E₀" => EuclideanSpace ℝ (Fin d)
theorem endpoint_bounds
    (U V : ℕ → Matrix (Fin d) (Fin d) ℝ) (lam : Fin d → ℝ)
    (hUV : ∀ t,U t*V t=1) (hVU : ∀ t,V t*U t=1)
    (S : Finset (Fin d)) (hSp : S.card=p) (n : ℕ) {γ g K C δ : ℝ}
    (hg : 0≤g) (hK : 0≤K) (hC : 0≤C) (hδ : 0≤δ)
    (hfast : ∀ j∈S,γ+g≤lam j) (hslow : ∀ j∉S,lam j≤γ-g)
    (hUs : ‖U 0‖≤Real.exp K) (hUt : ‖U n‖≤Real.exp K)
    (hVs : ‖V 0‖≤Real.exp K) (hVt : ‖V n‖≤Real.exp K)
    (hpoly : ∀ A : E₀ →L[ℝ] E₀,‖exterior p A‖≤C*(max 1 ‖A‖)^p)
    (W G Gslow : Submodule ℝ E₀) (hdim : Module.finrank ℝ W=p)
    (hend : ‖(groupSpace (U n) (V n) (hUV n) (hVU n) S).starProjection-W.starProjection‖≤1/2)
    (hstart : ‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) S).starProjection-G.starProjection‖≤δ)
    (hstartSlow : ‖(groupSpace (U 0) (V 0) (hUV 0) (hVU 0) Sᶜ).starProjection-Gslow.starProjection‖≤δ)
    (b : OrthonormalBasis (Fin d) ℝ E₀) (r : powersetCard (Fin d) p)
    (hr : ∀ j∈r,b j∈W) (hcoords : ∀ x∈W,∀ j∉r,b.repr x j=0)
    (v : Fin p → E₀) (horth : Orthonormal ℝ v) (hv : ∀ i,v i∈G)
    (z : Fin q → E₀) (hz : ∀ j,z j∈Gslow) (hznorm : ∀ j,‖z j‖≤1)
    (hsmall : (frameWedgeConstant (E := E₀) p*δ)*
      (1+((C*(Real.exp K)^p)^2*(C*2^p))*
        (C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p):ℝ))))≤1/2)
    (B : E₀ →L[ℝ] E₀) {ζ : ℝ} (hζ : 0≤ζ)
    (hpert : 2*((C*(Real.exp K)^p)^2*(C*2^p))*C*ζ*‖continuousWedge (E := E₀) p‖<1)
    (hdiff : ‖exterior p B-
      exterior p (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (transition U V lam 0 n))‖≤
        ζ*Real.exp ((n:ℝ)*(∑ j∈S,lam j))) :
    let A₀ := endpointMatrix b p r
      (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (transition U V lam 0 n)) v
    let A := endpointMatrix b p r B v
    let H := endpointMatrix b p r B z
    let L₀ := (C*(Real.exp K)^p)^2*(C*2^p)
    let N₀ := C*(C^2*(Real.exp K)^(2*p)*(Fintype.card (powersetCard (Fin d) p):ℝ))
    let N₁ := C*(C*(Real.exp K)^p)^2*(Fintype.card (powersetCard (Fin d) p):ℝ)*‖continuousWedge (E := E₀) p‖
    let θ := 2*L₀*(N₁*Real.exp (-2*g*n)+N₀*unitWedgeConstant (E := E₀) p*δ)
    let ε := 2*L₀*C*ζ*‖continuousWedge (E := E₀) p‖
    A₀.det≠0 ∧ A.det≠0 ∧ |A.det/A₀.det-1|≤ε ∧ ∀ i j,|(A⁻¹*H) i j|≤(θ+ε)/(1-ε) := by
  sorry
end SmoothObstruction.EuclideanSplitting

end

end OAI
end
