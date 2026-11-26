-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_brownian_ito_formula_for_locally_bounded_drift
-- name    : ManyServerQED.Scheduling.brownian_ito_formula_for_locally_bounded_drift
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:14:29.029232+00:00
-- url     : https://prove2.me/theorems/c0d21843-2bae-4114-881b-33fcc6ca7170
-- title:
--   Filtered Brownian Itô formula with measurable locally bounded drift
-- statement:
--   Let a standard multidimensional Brownian motion be adapted to a filtration, with future increments independent of the present. The multidimensional Itô formula holds for a continuous adapted process with continuous adapted Brownian diffusion coefficients and a jointly measurable drift whose paths are bounded on finite intervals.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_itoStepSum
import Definitions.Def_EthierKurtz_itoStepValue
import Definitions.Def_StochKolmogorov_Persist_Model
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators
open EthierKurtz
open Set

theorem ManyServerQED.Scheduling.brownian_ito_formula_for_locally_bounded_drift {Ω : Type*} [mΩ : MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W) (F : Filtration ℝ≥0 mΩ)
    (hWF : ∀ s : ℝ≥0, Indep (F s)
      (MeasurableSpace.comap (fun ω (p : ℝ≥0 × Fin d) => W (s + p.1) ω p.2 - W s ω p.2)
        inferInstance) P) (hFA : ∀ s : ℝ≥0, Measurable[F s] (W s)) :
    (∀ (j : Fin d) (H : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[F s] (H s)) →
      (∀ ω, Continuous fun s => H s ω) →
      ∃ J : ℝ≥0 → Ω → ℝ, HasBrownianItoIntegral P F
        (fun s ω => W s ω j) H J) ∧
    (∀ [IsProbabilityMeasure P] (j : Fin d) (H J : ℝ≥0 → Ω → ℝ),
      (∀ s, Measurable[F s] (H s)) →
      (∀ ω, Continuous fun s => H s ω) → ∀ C : ℝ, (∀ s ω, |H s ω| ≤ C) →
      HasBrownianItoIntegral P F
        (fun s ω => W s ω j) H J → ∀ t : ℝ≥0,
      MemLp (J t) 2 P ∧ ∫ ω, J t ω ^ 2 ∂P ≤ C ^ 2 * t ∧ ∫ ω, J t ω ∂P = 0) ∧
    (∀ [IsFiniteMeasure P] (e : ℕ) (X : ℝ≥0 → Ω → SDEState e),
      (∀ s, Measurable (X s)) → (∀ ω, Continuous fun s => X s ω) →
      (∀ s, Measurable[F s] (X s)) →
      ∀ (H J : Fin e → Fin d → ℝ≥0 → Ω → ℝ) (b : Fin e → ℝ≥0 → Ω → ℝ),
      (∀ i j s, Measurable[F s] (H i j s)) →
      (∀ i j ω, Continuous fun s => H i j s ω) →
      (∀ i j, HasBrownianItoIntegral P F
        (fun s ω => W s ω j) (H i j) (J i j)) →
      (∀ i, Measurable (fun z : Ω × ℝ≥0 => b i z.2 z.1)) →
      (∀ i ω (t : ℝ≥0), ∃ C : ℝ, ∀ u ∈ Set.Icc (0 : ℝ≥0) t, ‖b i u ω‖ ≤ C) →
      (∀ᵐ ω ∂P, ∀ (s : ℝ≥0) (i : Fin e), X s ω i = X 0 ω i + (∑ j, J i j s ω) +
        ∫ u in (0 : ℝ)..s.val, b i u.toNNReal ω) →
      ∀ (f : SDEState e → ℝ), ContDiff ℝ 2 f → ∀ (K : Fin e → Fin d → ℝ≥0 → Ω → ℝ),
      (∀ i j, HasBrownianItoIntegral P F
        (fun s ω => W s ω j)
        (fun s ω => fderiv ℝ f (X s ω) (EuclideanSpace.single i 1) * H i j s ω) (K i j)) →
      ∀ t : ℝ≥0,
      ∀ᵐ ω ∂P, f (X t ω) = f (X 0 ω) + (∑ i, ∑ j, K i j t ω) +
        (∑ i, ∫ u in (0 : ℝ)..t.val,
          fderiv ℝ f (X u.toNNReal ω) (EuclideanSpace.single i 1) * b i u.toNNReal ω) +
        (1 / 2) * ∑ i, ∑ i', ∑ j, ∫ u in (0 : ℝ)..t.val,
          fderiv ℝ (fderiv ℝ f) (X u.toNNReal ω) (EuclideanSpace.single i 1)
            (EuclideanSpace.single i' 1) * H i j u.toNNReal ω * H i' j u.toNNReal ω) := by sorry
