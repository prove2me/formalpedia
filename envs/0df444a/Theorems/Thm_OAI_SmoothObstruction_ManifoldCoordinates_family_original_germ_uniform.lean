-- Prove2me | Theorems.Thm_OAI_SmoothObstruction_ManifoldCoordinates_family_original_germ_uniform
-- name    : OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:16:20.069847+00:00
-- url     : https://prove2.me/theorems/9ef0e1e0-f293-4b3d-8ecc-6d329737281b
-- title:
--   OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform: intermediate lemma from OpenAI, Zero entropy does not guarantee a smooth positive-volume model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SmoothObstruction.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Zero entropy does not guarantee a smooth positive-volume model*, OpenAI Math Release, September 25, 2026, result family 152, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform` of [lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/GlobalSwitching.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/GlobalSwitching.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SmoothObstruction.ManifoldCoordinates`, with `open Set Metric Filter Topology EndpointFrame`, `open scoped Manifold ContDiff`):
--
--   ```lean
--   theorem family_original_germ_uniform (hclosed : IsClosed (range I))
--       (a : ι → M) (K : ι → Set M)
--       (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
--       ∃ r C β : ℝ,0 < r ∧ 1≤C ∧ 0<β ∧
--         ∀ {p q : ℕ},p≤d → q≤d →
--         ∀ {A J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
--           (P : M → A) (L : M → J) (R : Set M)
--           (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (ρ δ : ℝ)
--           (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
--           (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
--           0≤ρ → ρ ≤ r → C*ρ<δ →
--           (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
--           (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
--             originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
--             originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
--             originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
--           (∀ u∈R,∀ v∈R,L u=L v →
--             originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
--             originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
--             originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
--             originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
--           (∀ t : Fin (n+1),
--             closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
--             closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
--             closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
--             closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I)) →
--           let z := (Φ (x,y)).1
--           let w := (Φ (x,y)).2
--           originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
--           originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
--           let a₀ := a (c x)
--           let X := (extChartAt I a₀) x
--           let Y := (extChartAt I a₀) y
--           ∀ (U V : Submodule ℝ E₀) (_ : IsCompl U V)
--             (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V),
--             OriginalEndpointControl I S a c n ρ β (Wf (P x,P (S^[n] x))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) x →
--             OriginalEndpointControl I S a c n ρ β (Wf (P y,P (S^[n] y))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) y →
--             OriginalEndpointControl I S.symm a c n ρ β (Wb (P x,P (S.symm^[n] x))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) x →
--             OriginalEndpointControl I S.symm a c n ρ β (Wb (P y,P (S.symm^[n] y))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) y →
--             originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
--             originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w →
--             originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w →
--             originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
--             (∀ᶠ t in 𝓝 (X,Y),
--               P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
--               P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
--               P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
--               P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
--               P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
--             let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
--             let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
--             ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
--               (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
--               Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SmoothObstruction.ChartDensity.coordinates`, `OAI.SmoothObstruction.ChartDensity.inverse`, `OAI.SmoothObstruction.ChartDomination.coordinateSet`, `OAI.SmoothObstruction.ManifoldCoordinates.OriginalEndpointControl`, `OAI.SmoothObstruction.ManifoldCoordinates.originalEndpoint` and `OAI.SmoothObstruction.ManifoldCoordinates.originalTube` (definitions bundle `OAIQ5T3000` of this split).
--
--   **Used by.** The proof of `OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp` of this split imports it.
-- source:
--   OpenAI, Zero entropy does not guarantee a smooth positive-volume model, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 152; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/GlobalSwitching.lean (declaration OAI.SmoothObstruction.ManifoldCoordinates.family_original_germ_uniform)

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

namespace SmoothObstruction.ManifoldCoordinates
open Set Metric Filter Topology EndpointFrame
open scoped Manifold ContDiff
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

theorem family_original_germ_uniform (hclosed : IsClosed (range I))
    (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source) :
    ∃ r C β : ℝ,0 < r ∧ 1≤C ∧ 0<β ∧
      ∀ {p q : ℕ},p≤d → q≤d →
      ∀ {A J : Type*} (S : Diffeomorph I I M M ∞) (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (ρ δ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤ρ → ρ ≤ r → C*ρ<δ →
        (∀ u∈G,u.1∈R ∧ u.2∈R ∧ L u.1=L u.2) →
        (∀ u∈R,∀ v∈R,L u=L v → ∀ z,
          originalTube I S a c (n:=n) δ u z → originalTube I S.symm a c (n:=n) δ v z →
          originalEndpoint I S a c (n:=n) (Wf (P u,P (S^[n] u))) u z →
          originalEndpoint I S.symm a c (n:=n) (Wb (P v,P (S.symm^[n] v))) v z → z=(Φ (u,v)).1) →
        (∀ u∈R,∀ v∈R,L u=L v →
          originalTube I S a c (n:=n) δ v (Φ (u,v)).2 ∧
          originalTube I S.symm a c (n:=n) δ u (Φ (u,v)).2 ∧
          originalEndpoint I S a c (n:=n) (Wf (P v,P (S^[n] v))) v (Φ (u,v)).2 ∧
          originalEndpoint I S.symm a c (n:=n) (Wb (P u,P (S.symm^[n] u))) u (Φ (u,v)).2) →
        (∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) ρ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) ρ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        ∀ (U V : Submodule ℝ E₀) (_ : IsCompl U V)
          (u : OrthonormalBasis (Fin p) ℝ U) (v : OrthonormalBasis (Fin q) ℝ V),
          OriginalEndpointControl I S a c n ρ β (Wf (P x,P (S^[n] x))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) x →
          OriginalEndpointControl I S a c n ρ β (Wf (P y,P (S^[n] y))) (fun i => (u i:E₀)) (fun i => (v i:E₀)) y →
          OriginalEndpointControl I S.symm a c n ρ β (Wb (P x,P (S.symm^[n] x))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) x →
          OriginalEndpointControl I S.symm a c n ρ β (Wb (P y,P (S.symm^[n] y))) (fun i => (v i:E₀)) (fun i => (u i:E₀)) y →
          originalEndpoint I S a c (n:=n) (Wf (P x,P (S^[n] x))) x z →
          originalEndpoint I S a c (n:=n) (Wf (P y,P (S^[n] y))) y w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P x,P (S.symm^[n] x))) x w →
          originalEndpoint I S.symm a c (n:=n) (Wb (P y,P (S.symm^[n] y))) y z →
          (∀ᶠ t in 𝓝 (X,Y),
            P ((extChartAt I a₀).symm t.1)=P x ∧ P ((extChartAt I a₀).symm t.2)=P y ∧
            P (S^[n] ((extChartAt I a₀).symm t.1))=P (S^[n] x) ∧
            P (S^[n] ((extChartAt I a₀).symm t.2))=P (S^[n] y) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.1))=P (S.symm^[n] x) ∧
            P (S.symm^[n] ((extChartAt I a₀).symm t.2))=P (S.symm^[n] y)) →
          let e := Prod.map (ChartDensity.coordinates I a₀) (ChartDensity.coordinates I a₀)
          let s := Prod.map (ChartDensity.inverse I a₀) (ChartDensity.inverse I a₀)
          ∃ Ψ : E₀×E₀ → E₀×E₀,HasFDerivAt Ψ (fderiv ℝ Ψ (X,Y)) (X,Y) ∧
            (81/121:ℝ)≤|(fderiv ℝ Ψ (X,Y)).det| ∧
            Ψ =ᶠ[𝓝[ChartDomination.coordinateSet e s G] (X,Y)] (e ∘ Φ ∘ s) := by
  sorry
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end
