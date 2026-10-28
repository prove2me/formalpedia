-- Prove2me | Theorems.Thm_OAI_SmoothObstruction_ManifoldCoordinates_genuine_pair_switch
-- name    : OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:16:42.038412+00:00
-- url     : https://prove2.me/theorems/747db36d-8e15-4311-89be-50e1fb7726b5
-- title:
--   OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch: intermediate lemma from OpenAI, Zero entropy does not guarantee a smooth positive-volume model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SmoothObstruction.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Zero entropy does not guarantee a smooth positive-volume model*, OpenAI Math Release, September 25, 2026, result family 152, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch` of [lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/DensityLocalization.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/DensityLocalization.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SmoothObstruction.ManifoldCoordinates`, with `open Set Metric MeasureTheory Filter Topology EndpointFrame FiniteGreen ShortBin`, `open scoped Manifold ContDiff ENNReal`):
--
--   ```lean
--   theorem genuine_pair_switch (hclosed : IsClosed (range I))
--       (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
--       (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
--       (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
--       (s Dg : ℝ) (hs : 0 < s) (hDg : 0≤Dg) :
--       ∃ r₀ C₀ σ r₁ C₁ rg Cg β K₀F CreF C₁F K₀B CreB C₁B rμ : ℝ,
--         0 < r₀ ∧ 1≤C₀ ∧ 0<σ ∧ 0 < r₁ ∧ 1≤C₁ ∧ 0 < rg ∧ 1≤Cg ∧ 0<β ∧
--         1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧ 1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧ 0 < rμ ∧
--         ∀ {C J : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
--           [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
--           (c : M → ι) (P : M → C) (L : M → J) (π : J → C) (chart : C → ι)
--           (G R V Wc Wp : Set M) (n : ℕ) (b R₀ Cext ε g α r δc δp H₀ : ℝ)
--           (γ : C → ℝ),
--           let B := Dg*(b*n)
--           let δ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
--           let ρ := 2*C₀*bvpInverseBound B α n*r
--           let E := 4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
--             bvpInverseBound B α n*C₀*ρ^2
--           ∀ (A : ∀ x:G,BilateralGauge I S a c n B R₀ x) (T : G → Finset (Fin d)) (ref : G → G)
--             (Wf Wb : C×C → Submodule ℝ E₀),
--           Measurable c → Measurable P → Measurable L → MeasurableSet R → (hRG : R⊆G) →
--           (∀ x,x∈K (c x)) → (∀ x,π (L x)=P x) → (∀ x,chart (P x)=c x) →
--           (∀ x∈R,I.IsInteriorPoint x) →
--           (∀ x:G,P (ref x)=P x) → (∀ x y:G,P x=P y → (T x).card=(T y).card) →
--           (∀ x y:G,P x=P y → ref x=ref y) →
--           (∀ x:G,
--             ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
--               ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤ε ∧
--             ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
--               ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤ε) →
--           (∀ x:G,
--             Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
--             Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
--             ‖((A x).forwardSpace I S a c n (T x)).starProjection-
--               (Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
--             ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
--               (Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2) →
--           0≤b → 1≤b*n → 0≤R₀ → 0≤Cext → 0≤ε → ε≤1/2 →
--           Real.exp (2*B)*(2*ε)≤1/2 → 0≤g →
--           (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
--           (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
--           (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
--           (∀ x:G,|γ (P x)|+|g|≤α) → 0 ≤ r → δ ≤ r₀ → δ ≤ rg →
--           0≤ρ → ρ≤δ → ρ≤σ → ρ≤δc/4 → ρ ≤ r₁ → C₁*ρ≤δ → Cg*ρ<δ →
--           K₀F*δ≤1 → K₀B*δ≤1 → 0<δc → 0≤H₀ → H₀*E≤δp/4 →
--           (∀ p≤d,∀ F : E₀ →L[ℝ] E₀,‖ExteriorStability.exterior p F‖≤Cext*(max 1 ‖F‖)^p) →
--           (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀F CreF C₁F b n g ε β) →
--           (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀B CreB C₁B b n g ε β) →
--           (∀ x∈R,∀ t : Fin (n+1),
--             closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
--             closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
--           (∀ x∈R,∀ y∈R,L x=L y →
--             ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C₀*r) →
--           bvpInverseBound B α n*C₀*δ≤1/4 → bvpInverseBound B α n*C₀*r≤δ/4 →
--           (∀ x y,L x=L y → ‖ChartDensity.coordinates I (a (c x)) x-ChartDensity.coordinates I (a (c x)) y‖ < rμ) →
--           (∀ x∈V,∀ z,dist z x ≤ s → c z=c x) →
--           (∀ x z,x∉Wc → c z=c x →
--             ‖ChartDensity.coordinates I (a (c x)) z-ChartDensity.coordinates I (a (c x)) x‖≤δc/4 → P z=P x) →
--           (∀ x y z,(hx : x∈R) → L x=L y → x∉Wp → y∉Wp → P z=P x →
--             H₀*‖ChartDensity.coordinates I (a (c x)) z-(ChartDensity.coordinates I (a (c x)) x+
--               (((A (ref ⟨x,hRG hx⟩)).forward I S a c).splitting (T (ref ⟨x,hRG hx⟩))ᶜ).slow 0
--                 (ChartDensity.coordinates I (a (c x)) y-ChartDensity.coordinates I (a (c x)) x))‖≤δp/4 → L z=L x) →
--           (∀ x∈R,x∈V ∧ x∉Wc ∧ x∉Wp ∧
--             S^[n] x∈V ∧ S^[n] x∉Wc ∧ S.symm^[n] x∈V ∧ S.symm^[n] x∉Wc) →
--           let Gp := {u : M×M | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
--           ∃ Φ : M×M → M×M,Measurable Φ ∧ MeasurableSet Gp ∧ InjOn Φ Gp ∧
--             ((PairLaw.law μ L).restrict Gp).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L ∧
--             ((PairLaw.law μ L).restrict Gp).map (fun u => (Φ u).1)≤(2 : ℝ≥0∞) • μ ∧
--             ∀ u∈Gp,originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
--               originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1
--   ```
--
--   **Definitions.** The statement is written with `OAI.SmoothObstruction.ChartDensity.coordinates`, `OAI.SmoothObstruction.EndpointBudget.admissible`, `OAI.SmoothObstruction.EuclideanSplitting.evolution`, `OAI.SmoothObstruction.ExteriorStability.exterior`, `OAI.SmoothObstruction.ManifoldCoordinates.BilateralGauge`, `OAI.SmoothObstruction.ManifoldCoordinates.originalTube`, `OAI.SmoothObstruction.PairLaw.law`, `OAI.SmoothObstruction.ShortBin.bvpInverseBound`, `OAI.SmoothObstruction.SmoothScales.B`, `OAI.SmoothObstruction.FiniteGreen.Splitting`, `OAI.SmoothObstruction.ManifoldCoordinates.BilateralGauge.backwardSpace`, `OAI.SmoothObstruction.ManifoldCoordinates.BilateralGauge.forward`, `OAI.SmoothObstruction.ManifoldCoordinates.BilateralGauge.forwardSpace`, `OAI.SmoothObstruction.ShortBin.Gauge` and `OAI.SmoothObstruction.ShortBin.Gauge.splitting` (definitions bundle `OAIQ5T3000` of this split); `OAI.SmoothObstruction.SmoothPositiveDensity` (the published bundle `Def_SmoothObstruction`).
--
--   **Used by.** The proof of `OAI.SmoothObstruction.ManifoldCoordinates.grid_switches` of this split imports it.
-- source:
--   OpenAI, Zero entropy does not guarantee a smooth positive-volume model, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 152; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/DensityLocalization.lean (declaration OAI.SmoothObstruction.ManifoldCoordinates.genuine_pair_switch)

import Mathlib
import Definitions.Def_SmoothObstruction
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
open Set Metric MeasureTheory Filter Topology EndpointFrame FiniteGreen ShortBin
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
local notation "E₀" => EuclideanSpace ℝ (Fin d)

theorem genuine_pair_switch (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (S : Diffeomorph I I M M ∞) (a : ι → M) (K : ι → Set M)
    (hK : ∀ i,IsCompact (K i)) (hKU : ∀ i,K i⊆(chartAt H (a i)).source)
    (s Dg : ℝ) (hs : 0 < s) (hDg : 0≤Dg) :
    ∃ r₀ C₀ σ r₁ C₁ rg Cg β K₀F CreF C₁F K₀B CreB C₁B rμ : ℝ,
      0 < r₀ ∧ 1≤C₀ ∧ 0<σ ∧ 0 < r₁ ∧ 1≤C₁ ∧ 0 < rg ∧ 1≤Cg ∧ 0<β ∧
      1≤K₀F ∧ 0≤CreF ∧ 0≤C₁F ∧ 1≤K₀B ∧ 0≤CreB ∧ 0≤C₁B ∧ 0 < rμ ∧
      ∀ {C J : Type*} [Fintype C] [MeasurableSpace C] [MeasurableSingletonClass C]
        [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
        (c : M → ι) (P : M → C) (L : M → J) (π : J → C) (chart : C → ι)
        (G R V Wc Wp : Set M) (n : ℕ) (b R₀ Cext ε g α r δc δp H₀ : ℝ)
        (γ : C → ℝ),
        let B := Dg*(b*n)
        let δ := Real.exp (-(3/2:ℝ)*SmoothScales.B b*n)
        let ρ := 2*C₀*bvpInverseBound B α n*r
        let E := 4*Real.exp (2*B)*(2*Real.exp (2*B))*(ε+2*Real.exp (2*B)^2*Real.exp (-2*g*n))*(C₀*r)+
          bvpInverseBound B α n*C₀*ρ^2
        ∀ (A : ∀ x:G,BilateralGauge I S a c n B R₀ x) (T : G → Finset (Fin d)) (ref : G → G)
          (Wf Wb : C×C → Submodule ℝ E₀),
        Measurable c → Measurable P → Measurable L → MeasurableSet R → (hRG : R⊆G) →
        (∀ x,x∈K (c x)) → (∀ x,π (L x)=P x) → (∀ x,chart (P x)=c x) →
        (∀ x∈R,I.IsInteriorPoint x) →
        (∀ x:G,P (ref x)=P x) → (∀ x y:G,P x=P y → (T x).card=(T y).card) →
        (∀ x y:G,P x=P y → ref x=ref y) →
        (∀ x:G,
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))ᶜ).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)ᶜ).starProjection‖≤ε ∧
          ‖((A (ref x)).forwardSpace I S a c 0 (T (ref x))).starProjection-
            ((A x).forwardSpace I S a c 0 (T x)).starProjection‖≤ε) →
        (∀ x:G,
          Module.finrank ℝ (Wf (P x,P (S^[n] x)))=(T x).card ∧
          Module.finrank ℝ (Wb (P x,P (S.symm^[n] x)))=d-(T x).card ∧
          ‖((A x).forwardSpace I S a c n (T x)).starProjection-
            (Wf (P x,P (S^[n] x))).starProjection‖≤1/2 ∧
          ‖((A x).backwardSpace I S a c n (T x)ᶜ).starProjection-
            (Wb (P x,P (S.symm^[n] x))).starProjection‖≤1/2) →
        0≤b → 1≤b*n → 0≤R₀ → 0≤Cext → 0≤ε → ε≤1/2 →
        Real.exp (2*B)*(2*ε)≤1/2 → 0≤g →
        (∀ x:G,∀ j∈(T x)ᶜ,(A x).lam j≤γ (P x)-g) →
        (∀ x:G,∀ j∈T x,γ (P x)+g≤(A x).lam j) →
        (2*Real.exp (2*B))*(2*(2*Real.exp (2*B)^2*Real.exp (-2*g*n)))≤1/2 →
        (∀ x:G,|γ (P x)|+|g|≤α) → 0 ≤ r → δ ≤ r₀ → δ ≤ rg →
        0≤ρ → ρ≤δ → ρ≤σ → ρ≤δc/4 → ρ ≤ r₁ → C₁*ρ≤δ → Cg*ρ<δ →
        K₀F*δ≤1 → K₀B*δ≤1 → 0<δc → 0≤H₀ → H₀*E≤δp/4 →
        (∀ p≤d,∀ F : E₀ →L[ℝ] E₀,‖ExteriorStability.exterior p F‖≤Cext*(max 1 ‖F‖)^p) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀F CreF C₁F b n g ε β) →
        (∀ p≤d,EndpointBudget.admissible d p Dg R₀ Cext K₀B CreB C₁B b n g ε β) →
        (∀ x∈R,∀ t : Fin (n+1),
          closedBall ((extChartAt I (a (c (S^[t.val] x)))) (S^[t.val] x)) δ⊆interior (range I) ∧
          closedBall ((extChartAt I (a (c (S.symm^[t.val] x)))) (S.symm^[t.val] x)) δ⊆interior (range I)) →
        (∀ x∈R,∀ y∈R,L x=L y →
          ‖(extChartAt I (a (c y))) y-(extChartAt I (a (c x))) x‖≤C₀*r) →
        bvpInverseBound B α n*C₀*δ≤1/4 → bvpInverseBound B α n*C₀*r≤δ/4 →
        (∀ x y,L x=L y → ‖ChartDensity.coordinates I (a (c x)) x-ChartDensity.coordinates I (a (c x)) y‖ < rμ) →
        (∀ x∈V,∀ z,dist z x ≤ s → c z=c x) →
        (∀ x z,x∉Wc → c z=c x →
          ‖ChartDensity.coordinates I (a (c x)) z-ChartDensity.coordinates I (a (c x)) x‖≤δc/4 → P z=P x) →
        (∀ x y z,(hx : x∈R) → L x=L y → x∉Wp → y∉Wp → P z=P x →
          H₀*‖ChartDensity.coordinates I (a (c x)) z-(ChartDensity.coordinates I (a (c x)) x+
            (((A (ref ⟨x,hRG hx⟩)).forward I S a c).splitting (T (ref ⟨x,hRG hx⟩))ᶜ).slow 0
              (ChartDensity.coordinates I (a (c x)) y-ChartDensity.coordinates I (a (c x)) x))‖≤δp/4 → L z=L x) →
        (∀ x∈R,x∈V ∧ x∉Wc ∧ x∉Wp ∧
          S^[n] x∈V ∧ S^[n] x∉Wc ∧ S.symm^[n] x∈V ∧ S.symm^[n] x∉Wc) →
        let Gp := {u : M×M | u.1∈R ∧ u.2∈R ∧ L u.1=L u.2}
        ∃ Φ : M×M → M×M,Measurable Φ ∧ MeasurableSet Gp ∧ InjOn Φ Gp ∧
          ((PairLaw.law μ L).restrict Gp).map Φ≤(2 : ℝ≥0∞) • PairLaw.law μ L ∧
          ((PairLaw.law μ L).restrict Gp).map (fun u => (Φ u).1)≤(2 : ℝ≥0∞) • μ ∧
          ∀ u∈Gp,originalTube I S a c (n:=n) ρ u.1 (Φ u).1 ∧
            originalTube I S.symm a c (n:=n) ρ u.2 (Φ u).1 := by
  sorry
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end
