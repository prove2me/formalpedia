-- Prove2me | Theorems.Thm_OAI_SmoothObstruction_ManifoldCoordinates_grid_switches
-- name    : OAI.SmoothObstruction.ManifoldCoordinates.grid_switches
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T10:18:20.826394+00:00
-- url     : https://prove2.me/theorems/592a4dc7-99c1-48d7-893e-2506b2104c75
-- title:
--   OAI.SmoothObstruction.ManifoldCoordinates.grid_switches: intermediate lemma from OpenAI, Zero entropy does not guarantee a smooth positive-volume model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SmoothObstruction.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Zero entropy does not guarantee a smooth positive-volume model*, OpenAI Math Release, September 25, 2026, result family 152, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SmoothObstruction.ManifoldCoordinates.grid_switches` of [lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/Counting.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/Counting.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SmoothObstruction.ManifoldCoordinates`, with `open Set Metric Filter Topology MeasureTheory`, `open scoped Manifold ContDiff ENNReal`):
--
--   ```lean
--   theorem grid_switches (hclosed : IsClosed (range I))
--       (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
--       (S : Diffeomorph I I M M ∞) (hS : MeasurePreserving S μ μ)
--       (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
--       (hKU : ∀ i,K i⊆(chartAt H (a i)).source) (c : M → ι) (hc : Measurable c)
--       (hcover : ∀ x,x∈K (c x)) (V : Set M) (hV : MeasurableSet V)
--       (s : ℝ) (hs : 0 < s) (hcore : ∀ x∈V,∀ y,dist y x ≤ s → c y=c x)
--       (η : ℝ) (hη : 0<η) (hVm : μ.real Vᶜ≤η/100)
--       (b : ℕ → ℝ) (n : ℕ → ℕ) (hbpos : ∀ k,0<b k) (hb : Tendsto b atTop (𝓝 0))
--       (hn : Tendsto (fun k => (n k:ℝ)) atTop atTop)
--       (hfloor : ∀ k,(n k:ℝ)^(-1/10:ℝ)≤b k)
--       (Dg R₀ : ℝ) (hDg : 0≤Dg) (hR₀ : 0≤R₀)
--       (G : ℕ → Set M) (hG : ∀ k,MeasurableSet (G k)) (hGm : ∀ k,μ.real (G k)ᶜ≤η/100)
--       (hA : ∀ᶠ k in atTop,∀ x∈G k,Nonempty (BilateralGauge I S a c (n k) (Dg*(b k*n k)) R₀ x))
--       (Cb : ℝ) (_ : 0≤Cb)
--       (hcollar : ∀ r : ℝ,0 ≤ r → ∃ W : Set M,MeasurableSet W ∧ μ.real W≤Cb*r ∧
--         ∀ i x,x∈K i → x∉W → closedBall ((extChartAt I (a i)) x) r⊆interior (range I)) :
--       ∃ (Dc Dp : ℝ) (N : ℕ) (ρ : ℕ → ℝ),1≤Dc ∧ 1≤Dp ∧ 0<N ∧
--         Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
--         let B := Dg*(b k*n k)
--         let h₀ := Real.exp (-b k^(1/8:ℝ)*n k)
--         let r := Real.exp (-2*b k^(1/8:ℝ)*n k)
--         let δc := h₀/(((d:ℝ)+1)*N)
--         let δp := r/(Real.sqrt 2*((d:ℝ)+1)*N)
--         let mc := ⌈Dc/(δc*N)+1⌉₊
--         let mp := ⌈(Real.sqrt 2*Real.exp (2*B))*Dp/(δp*N)+1⌉₊
--         ∃ (J : Type) (_ : Fintype J) (_ : MeasurableSpace J) (_ : MeasurableSingletonClass J)
--           (L : M → J) (Gp : Set (M×M)) (Φ : M×M → M×M),
--           Fintype.card J=Fintype.card ι*(2*mc+1)^d*(2*mp+1)^d ∧
--           Measurable L ∧ MeasurableSet Gp ∧ Measurable Φ ∧
--           1-η≤(PairLaw.law μ L).real Gp ∧
--           ((PairLaw.law μ L).restrict Gp).map (fun u => (Φ u).1)≤(2:ℝ≥0∞) • μ ∧
--           ∀ u∈Gp,originalTube I S a c (n:=n k) (ρ k) u.1 (Φ u).1 ∧
--             originalTube I S.symm a c (n:=n k) (ρ k) u.2 (Φ u).1
--   ```
--
--   **Definitions.** The statement is written with `OAI.SmoothObstruction.ManifoldCoordinates.BilateralGauge`, `OAI.SmoothObstruction.ManifoldCoordinates.originalTube` and `OAI.SmoothObstruction.PairLaw.law` (definitions bundle `OAIQ5T3000` of this split); `OAI.SmoothObstruction.SmoothPositiveDensity` (the published bundle `Def_SmoothObstruction`).
--
--   **Used by.** The proof of `OAI.SmoothObstruction.main` of this split imports it.
-- source:
--   OpenAI, Zero entropy does not guarantee a smooth positive-volume model, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 152; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finite-entropy-system-without-a-smooth-positive-volume-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/SmoothObstruction/SmoothObstruction/Counting.lean (declaration OAI.SmoothObstruction.ManifoldCoordinates.grid_switches)

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
open Set Metric Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal
variable {d : ℕ} {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin d)) H)
    {M : Type*} [MetricSpace M] [ProperSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [MeasurableSpace M] [BorelSpace M] [StandardBorelSpace M] [Nonempty M]
    {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem grid_switches (hclosed : IsClosed (range I))
    (μ : Measure M) [IsProbabilityMeasure μ] (hμ : SmoothPositiveDensity I μ)
    (S : Diffeomorph I I M M ∞) (hS : MeasurePreserving S μ μ)
    (a : ι → M) (K : ι → Set M) (hK : ∀ i,IsCompact (K i))
    (hKU : ∀ i,K i⊆(chartAt H (a i)).source) (c : M → ι) (hc : Measurable c)
    (hcover : ∀ x,x∈K (c x)) (V : Set M) (hV : MeasurableSet V)
    (s : ℝ) (hs : 0 < s) (hcore : ∀ x∈V,∀ y,dist y x ≤ s → c y=c x)
    (η : ℝ) (hη : 0<η) (hVm : μ.real Vᶜ≤η/100)
    (b : ℕ → ℝ) (n : ℕ → ℕ) (hbpos : ∀ k,0<b k) (hb : Tendsto b atTop (𝓝 0))
    (hn : Tendsto (fun k => (n k:ℝ)) atTop atTop)
    (hfloor : ∀ k,(n k:ℝ)^(-1/10:ℝ)≤b k)
    (Dg R₀ : ℝ) (hDg : 0≤Dg) (hR₀ : 0≤R₀)
    (G : ℕ → Set M) (hG : ∀ k,MeasurableSet (G k)) (hGm : ∀ k,μ.real (G k)ᶜ≤η/100)
    (hA : ∀ᶠ k in atTop,∀ x∈G k,Nonempty (BilateralGauge I S a c (n k) (Dg*(b k*n k)) R₀ x))
    (Cb : ℝ) (_ : 0≤Cb)
    (hcollar : ∀ r : ℝ,0 ≤ r → ∃ W : Set M,MeasurableSet W ∧ μ.real W≤Cb*r ∧
      ∀ i x,x∈K i → x∉W → closedBall ((extChartAt I (a i)) x) r⊆interior (range I)) :
    ∃ (Dc Dp : ℝ) (N : ℕ) (ρ : ℕ → ℝ),1≤Dc ∧ 1≤Dp ∧ 0<N ∧
      Tendsto ρ atTop (𝓝 0) ∧ ∀ᶠ k in atTop,
      let B := Dg*(b k*n k)
      let h₀ := Real.exp (-b k^(1/8:ℝ)*n k)
      let r := Real.exp (-2*b k^(1/8:ℝ)*n k)
      let δc := h₀/(((d:ℝ)+1)*N)
      let δp := r/(Real.sqrt 2*((d:ℝ)+1)*N)
      let mc := ⌈Dc/(δc*N)+1⌉₊
      let mp := ⌈(Real.sqrt 2*Real.exp (2*B))*Dp/(δp*N)+1⌉₊
      ∃ (J : Type) (_ : Fintype J) (_ : MeasurableSpace J) (_ : MeasurableSingletonClass J)
        (L : M → J) (Gp : Set (M×M)) (Φ : M×M → M×M),
        Fintype.card J=Fintype.card ι*(2*mc+1)^d*(2*mp+1)^d ∧
        Measurable L ∧ MeasurableSet Gp ∧ Measurable Φ ∧
        1-η≤(PairLaw.law μ L).real Gp ∧
        ((PairLaw.law μ L).restrict Gp).map (fun u => (Φ u).1)≤(2:ℝ≥0∞) • μ ∧
        ∀ u∈Gp,originalTube I S a c (n:=n k) (ρ k) u.1 (Φ u).1 ∧
          originalTube I S.symm a c (n:=n k) (ρ k) u.2 (Φ u).1 := by
  sorry
end SmoothObstruction.ManifoldCoordinates

end

end OAI
end
