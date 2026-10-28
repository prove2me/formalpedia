-- Prove2me | Theorems.Thm_OAI_SmoothObstruction_ManifoldCoordinates_gauge_original_germ_sharp
-- name    : OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:16:43.156494+00:00
-- url     : https://prove2.me/theorems/c55410d5-36f1-4da3-97ca-2e3ea4e6bd17
-- title:
--   OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp: intermediate lemma from OpenAI, Zero entropy does not guarantee a smooth positive-volume model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SmoothObstruction.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Zero entropy does not guarantee a smooth positive-volume model*, OpenAI Math Release, September 25, 2026, result family 152, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp` of [lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/GlobalSwitching.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/GlobalSwitching.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SmoothObstruction.ManifoldCoordinates`, with `open Set Metric Filter Topology EndpointFrame`, `open scoped Manifold ContDiff`):
--
--   ```lean
--   theorem gauge_original_germ_sharp (hclosed : IsClosed (range I))
--       (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
--       (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
--       (Dg : ℝ) (hDg : 0≤Dg) :
--       ∃ r Cg β K₀F CreF C₁F K₀B CreB C₁B : ℝ,
--         0 < r ∧ 1≤Cg ∧ 0<β ∧ 1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧
--         1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧
--         ∀ {A J : Type*} (c : M → ι)
--           (P : M → A) (L : M → J) (R : Set M)
--           (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (b R₀ Cext δ ε γ g ρ : ℝ)
--           (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
--           let σ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
--           (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
--           0≤b → 1≤b*n → 0≤R₀ → 0≤Cext → 0≤ε → 0≤g →
--           0≤ρ → ρ≤σ → σ ≤ r → Cg*ρ<δ → K₀F*σ≤1 → K₀B*σ≤1 →
--           (∀ p≤d,∀ B : E₀ →L[ℝ] E₀,‖ExteriorStability.exterior p B‖≤Cext*(max 1 ‖B‖)^p) →
--           (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀F CreF C₁F b n g ε β) →
--           (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀B CreB C₁B b n g ε β) →
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
--             closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) σ⊆interior (range I) ∧
--             closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) σ⊆interior (range I) ∧
--             closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) σ⊆interior (range I) ∧
--             closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) σ⊆interior (range I)) →
--           let z := (Φ (x,y)).1
--           let w := (Φ (x,y)).2
--           originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
--           originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
--           let a₀ := a (c x)
--           let X := (extChartAt I a₀) x
--           let Y := (extChartAt I a₀) y
--           ∀ (x₀ : M) (Ar : BilateralGauge I S a c n (Dg*(b*n)) R₀ x₀)
--             (Ax : BilateralGauge I S a c n (Dg*(b*n)) R₀ x)
--             (Ay : BilateralGauge I S a c n (Dg*(b*n)) R₀ y)
--             (Tr Tx Ty : Finset (Fin d)),Tx.card=Tr.card → Ty.card=Tr.card →
--             (∀ j∈Tx,γ+g≤Ax.lam j) → (∀ j∉Tx,Ax.lam j≤γ-g) →
--             (∀ j∈Ty,γ+g≤Ay.lam j) → (∀ j∉Ty,Ay.lam j≤γ-g) →
--             Module.finrank ℝ (Wf (P x,P (S^[n] x)))=Tr.card →
--             Module.finrank ℝ (Wf (P y,P (S^[n] y)))=Tr.card →
--             Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-Tr.card →
--             Module.finrank ℝ (Wb (P y,P (S.symm^[n] y)))=d-Tr.card →
--             ‖(Ax.forwardSpace I S a c n Tx).starProjection-(Wf (P x,P (S^[n] x))).starProjection‖≤1/2 →
--             ‖(Ay.forwardSpace I S a c n Ty).starProjection-(Wf (P y,P (S^[n] y))).starProjection‖≤1/2 →
--             ‖(Ax.backwardSpace I S a c n Txᶜ).starProjection-(Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2 →
--             ‖(Ay.backwardSpace I S a c n Tyᶜ).starProjection-(Wb (P y,P (S.symm^[n] y))).starProjection‖≤1/2 →
--             ‖(Ax.forwardSpace I S a c 0 Tx).starProjection-(Ar.forwardSpace I S a c 0 Tr).starProjection‖≤ε →
--             ‖(Ay.forwardSpace I S a c 0 Ty).starProjection-(Ar.forwardSpace I S a c 0 Tr).starProjection‖≤ε →
--             ‖(Ax.forwardSpace I S a c 0 Txᶜ).starProjection-(Ar.forwardSpace I S a c 0 Trᶜ).starProjection‖≤ε →
--             ‖(Ay.forwardSpace I S a c 0 Tyᶜ).starProjection-(Ar.forwardSpace I S a c 0 Trᶜ).starProjection‖≤ε →
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
--   **Definitions.** The statement is written with `OAI.SmoothObstruction.ChartDensity.coordinates`, `OAI.SmoothObstruction.ChartDensity.inverse`, `OAI.SmoothObstruction.ChartDomination.coordinateSet`, `OAI.SmoothObstruction.EndpointBudget.admissible`, `OAI.SmoothObstruction.ExteriorStability.exterior`, `OAI.SmoothObstruction.ManifoldCoordinates.BilateralGauge`, `OAI.SmoothObstruction.ManifoldCoordinates.originalEndpoint`, `OAI.SmoothObstruction.ManifoldCoordinates.originalTube`, `OAI.SmoothObstruction.SmoothScales.B`, `OAI.SmoothObstruction.ManifoldCoordinates.BilateralGauge.backwardSpace` and `OAI.SmoothObstruction.ManifoldCoordinates.BilateralGauge.forwardSpace` (definitions bundle `OAIQ5T3000` of this split).
--
--   **Used by.** The proof of `OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch` of this split imports it.
-- source:
--   OpenAI, Zero entropy does not guarantee a smooth positive-volume model, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 152; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/GlobalSwitching.lean (declaration OAI.SmoothObstruction.ManifoldCoordinates.gauge_original_germ_sharp)

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
    [MeasurableSpace M] [BorelSpace M]
    {ι : Type*} [Fintype ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

omit [MeasurableSpace M] [BorelSpace M] in
theorem gauge_original_germ_sharp (hclosed : IsClosed (range I))
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (Dg : ℝ) (hDg : 0≤Dg) :
    ∃ r Cg β K₀F CreF C₁F K₀B CreB C₁B : ℝ,
      0 < r ∧ 1≤Cg ∧ 0<β ∧ 1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧
      1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧
      ∀ {A J : Type*} (c : M → ι)
        (P : M → A) (L : M → J) (R : Set M)
        (Wf Wb : A×A → Submodule ℝ E₀) (n : ℕ) (b R₀ Cext δ ε γ g ρ : ℝ)
        (Φ : M×M → M×M) (G : Set (M×M)) (x y : M),
        let σ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        (∀ z,z∈K (c z)) → (∀ u v,P u=P v → c u=c v) → c x=c y →
        0≤b → 1≤b*n → 0≤R₀ → 0≤Cext → 0≤ε → 0≤g →
        0≤ρ → ρ≤σ → σ ≤ r → Cg*ρ<δ → K₀F*σ≤1 → K₀B*σ≤1 →
        (∀ p≤d,∀ B : E₀ →L[ℝ] E₀,‖ExteriorStability.exterior p B‖≤Cext*(max 1 ‖B‖)^p) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀F CreF C₁F b n g ε β) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀B CreB C₁B b n g ε β) →
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
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S^[t.val] y)))) (S^[t.val] y)) σ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] y)))) (S.symm^[t.val] y)) σ⊆interior (range I)) →
        let z := (Φ (x,y)).1
        let w := (Φ (x,y)).2
        originalTube I S a c (n:=n) ρ x z → originalTube I S.symm a c (n:=n) ρ y z →
        originalTube I S a c (n:=n) ρ y w → originalTube I S.symm a c (n:=n) ρ x w →
        let a₀ := a (c x)
        let X := (extChartAt I a₀) x
        let Y := (extChartAt I a₀) y
        ∀ (x₀ : M) (Ar : BilateralGauge I S a c n (Dg*(b*n)) R₀ x₀)
          (Ax : BilateralGauge I S a c n (Dg*(b*n)) R₀ x)
          (Ay : BilateralGauge I S a c n (Dg*(b*n)) R₀ y)
          (Tr Tx Ty : Finset (Fin d)),Tx.card=Tr.card → Ty.card=Tr.card →
          (∀ j∈Tx,γ+g≤Ax.lam j) → (∀ j∉Tx,Ax.lam j≤γ-g) →
          (∀ j∈Ty,γ+g≤Ay.lam j) → (∀ j∉Ty,Ay.lam j≤γ-g) →
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=Tr.card →
          Module.finrank ℝ (Wf (P y,P (S^[n] y)))=Tr.card →
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-Tr.card →
          Module.finrank ℝ (Wb (P y,P (S.symm^[n] y)))=d-Tr.card →
          ‖(Ax.forwardSpace I S a c n Tx).starProjection-(Wf (P x,P (S^[n] x))).starProjection‖≤1/2 →
          ‖(Ay.forwardSpace I S a c n Ty).starProjection-(Wf (P y,P (S^[n] y))).starProjection‖≤1/2 →
          ‖(Ax.backwardSpace I S a c n Txᶜ).starProjection-(Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2 →
          ‖(Ay.backwardSpace I S a c n Tyᶜ).starProjection-(Wb (P y,P (S.symm^[n] y))).starProjection‖≤1/2 →
          ‖(Ax.forwardSpace I S a c 0 Tx).starProjection-(Ar.forwardSpace I S a c 0 Tr).starProjection‖≤ε →
          ‖(Ay.forwardSpace I S a c 0 Ty).starProjection-(Ar.forwardSpace I S a c 0 Tr).starProjection‖≤ε →
          ‖(Ax.forwardSpace I S a c 0 Txᶜ).starProjection-(Ar.forwardSpace I S a c 0 Trᶜ).starProjection‖≤ε →
          ‖(Ay.forwardSpace I S a c 0 Tyᶜ).starProjection-(Ar.forwardSpace I S a c 0 Trᶜ).starProjection‖≤ε →
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
