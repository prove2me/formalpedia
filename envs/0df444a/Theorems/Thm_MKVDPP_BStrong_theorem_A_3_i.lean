-- Prove2me | Theorems.Thm_MKVDPP_BStrong_theorem_A_3_i
-- name    : MKVDPP.BStrong.theorem_A_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T13:25:08.312654+00:00
-- url     : https://prove2.me/theorems/5c1a17a3-ef71-4ce9-b0aa-12b710896f0c
-- title:
--   Theorem A.3(i) — strong solution existence and uniqueness
-- statement:
--   Assume the Lipschitz and growth conditions of Assumption 2.8. On a complete filtered probability space, fix two independent Brownian motions, an adapted continuous initial process $\xi$, a predictable control $\alpha$, and a complete common noise subfiltration. If $q\ge2$, the initial stopped path has finite $q$th supremum moment, and the control has finite $q$th energy, then equation (A.1) has a strong solution, unique up to indistinguishability, with
--
--   $$\mathbb E\!\left[\sup_{0\le s\le T}|X_s|^q\right]<\infty.$$
--
--   This gives the strong state process required by the fixed space value.
--
--   **Formalization Note** Noise dimensions follow equation (A.1), correcting the swapped dimensions in the appendix preamble.
-- source:
--   Djete, Possamaï, Tan, McKean–Vlasov optimal control: the dynamic programming principle, arXiv:1907.08860v2, p. 27, Theorem A.3(i), equation (A.1)

import Definitions.Def_MKVDPP_BStrong_FixedSpace

open MeasureTheory ProbabilityTheory Filter Classical
open scoped ENNReal NNReal Topology BigOperators

namespace MKVDPP.BStrong

/-- Theorem A.3(i), p. 27: existence, pathwise uniqueness and q-moment
control for the conditional McKean–Vlasov SDE (A.1). -/
theorem theorem_A_3_i {T : ℝ≥0} (hT : 0 < T) {n d ell : ℕ}
    {U Ω : Type*} [MetricSpace U] [CompleteSpace U]
    [TopologicalSpace.SeparableSpace U] [Nonempty U]
    [MeasurableSpace U] [BorelSpace U] [MeasurableSpace Ω]
    (M : Model T n d ell U) (hA : Assumption28 T n d ell M.u₀ M.b M.σ M.σ₀)
    (P : Measure Ω) [IsProbabilityMeasure P] (hcomplete : P.IsComplete)
    (F G : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (hFcomplete : ∀ s, augmented P (F s) = F s)
    (hGcomplete : ∀ s, augmented P (G s) = G s)
    (hGsub : ∀ s, G s ≤ F s)
    (t : ℝ≥0) (ht : t ≤ T) (q : ℝ) (hq : 2 ≤ q)
    (ξ : Ω → Cpath T n) (hξ : ∀ s, s ≤ T →
      Measurable[F s] (fun ω => pathAt (ξ ω) s))
    (α : ℝ≥0 → Ω → U)
    (hα : Measurable[F.predictable] (fun z : ℝ≥0 × Ω => α z.1 z.2))
    (W : Ω → Cpath T d) (B : Ω → Cpath T ell)
    (hW : IsFBrownianOn F P 0 T (fun s ω => pathAt (W ω) s))
    (hB : IsFBrownianOn F P 0 T (fun s ω => pathAt (B ω) s))
    (hW0 : P {ω | pathAt (W ω) 0 = 0} = 1)
    (hB0 : P {ω | pathAt (B ω) 0 = 0} = 1)
    (hWB : Indep (MeasurableSpace.comap W inferInstance)
      (MeasurableSpace.comap B inferInstance) P)
    (hξq : ∫⁻ ω, ENNReal.ofReal (‖stopPath t (ξ ω)‖ ^ q) ∂P < ⊤)
    (hαq : ∫⁻ ω, ∫⁻ s in Set.Icc (t : ℝ) (T : ℝ),
      edist (α s.toNNReal ω) M.u₀ ^ q ∂volume ∂P < ⊤) :
    ∃ (X : Ω → Cpath T n)
      (μbar : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)),
      IsStrongSolution M P F G t ξ X W B α μbar ∧
      (∫⁻ ω, ENNReal.ofReal (‖X ω‖ ^ q) ∂P) < ⊤ ∧
      ∀ (X' : Ω → Cpath T n)
        (μbar' : ℝ≥0 → Ω → ProbabilityMeasure (Cpath T n × U)),
        IsStrongSolution M P F G t ξ X' W B α μbar' → X =ᵐ[P] X' := by sorry

end MKVDPP.BStrong
