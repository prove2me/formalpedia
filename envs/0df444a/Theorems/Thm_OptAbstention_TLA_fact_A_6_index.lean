-- Prove2me | Theorems.Thm_OptAbstention_TLA_fact_A_6_index
-- name    : OptAbstention.TLA.fact_A_6_index
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:20:10.907198+00:00
-- url     : https://prove2.me/theorems/17a5f774-a11a-4296-a7ab-90ac6848e36c
-- title:
--   Fact A.6 with V + 1 (corrected: the printed bound vanishes at VC-subgraph dimension 0)
-- statement:
--   **Source:** Fact A.6 with right-hand side $C \cdot \sqrt{V\, \mathbb{E}_D[F^2]/n}$, $V$ the VC-subgraph dimension.
--
--   **Variant:** $V$ is replaced by $V + 1$ (the VC index used by van der Vaart and Wellner).
--
--   **Difference:** the two coincide up to the constant for $V \ge 1$ and differ only at $V = 0$, where the printed bound is $0$.
-- source:
--   Chandrasekaran, Gkrinias, Klivans, Stavropoulos, Vasilyan, Achieving the Optimal Abstention Rate for Learning with Distribution Shift, STOC 2027 submission (manuscript sha256 0fb30af1…), p. 35, Fact A.6 (corrected)

import Mathlib
import Definitions.Def_OptAbstention_TLA_CappedReweighting
open MeasureTheory

namespace OptAbstention.TLA

/-- Fact A.6, p. 35: for a pointwise measurable class `F` of measurable functions with
VC-subgraph dimension `V` and envelope `F_env`,
`E_{S∼D^n}[sup_{f∈F} |E_{U(S)} f − E_D f|] ≤ C √(V E_D[F_env²]/n)`, `C` universal. -/
theorem fact_A_6_index : ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (D : Measure Ω) [IsProbabilityMeasure D]
      (F : Set (Ω → ℝ)) (V : ℕ) (Fenv : Ω → ℝ),
      PointwiseMeasurableClass F → (∀ f ∈ F, Measurable f) → vcSubgraphDim F ≤ V →
      Measurable Fenv → (∀ x, 0 ≤ Fenv x) → (∀ f ∈ F, ∀ x, |f x| ≤ Fenv x) →
      ∀ n : ℕ, 1 ≤ n →
      ∫⁻ S, (⨆ f ∈ F, ENNReal.ofReal |(∑ i, f (S i)) / n - ∫ x, f x ∂D|)
          ∂(Measure.pi fun _ : Fin n => D) ≤
        ENNReal.ofReal C *
          (((V + 1 : ℕ) : ENNReal) * (∫⁻ x, ENNReal.ofReal (Fenv x ^ 2) ∂D) / n) ^ (1 / 2 : ℝ) := by sorry

end OptAbstention.TLA
