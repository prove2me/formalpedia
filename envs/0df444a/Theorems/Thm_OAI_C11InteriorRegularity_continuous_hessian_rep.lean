-- Prove2me | Theorems.Thm_OAI_C11InteriorRegularity_continuous_hessian_rep
-- name    : OAI.C11InteriorRegularity.continuous_hessian_rep
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T05:14:02.333974+00:00
-- url     : https://prove2.me/theorems/8417c140-b798-40d0-acd6-0bd8f671c7dd
-- title:
--   OAI.C11InteriorRegularity.continuous_hessian_rep: intermediate lemma from OpenAI, The logarithmic Brunn–Minkowski conjecture
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.LogBrunnMinkowski.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The logarithmic Brunn–Minkowski conjecture*, OpenAI Math Release, September 23, 2026, result family 91, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.C11InteriorRegularity.continuous_hessian_rep` of [lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.C11InteriorRegularity`, with `open Set MeasureTheory Filter`, `open scoped InnerProductSpace Topology NNReal`, `open Set Filter`, `open scoped Topology NNReal`, `open Set MeasureTheory Filter`, `open scoped Topology NNReal ENNReal`, `open scoped ENNReal`, `open scoped InnerProductSpace ContDiff Topology`, `open scoped ENNReal`, `open Set MeasureTheory Filter`, `open scoped ENNReal Topology`, `open Set MeasureTheory Filter`, `open scoped InnerProductSpace Topology`, `open Set MeasureTheory Filter`, `open scoped Topology BoundedContinuousFunction`, `open Set MeasureTheory Filter`, `open scoped InnerProductSpace Topology`, `open Set Filter Metric Matrix MeasureTheory OscillationEnvelope FiniteElliptic`, `open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise`):
--
--   ```lean
--   theorem continuous_hessian_rep (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} {L : ℝ≥0}
--       (hd : Differentiable ℝ φ) (hL : LipschitzWith L (gradient φ))
--       {A : E → Mat} {β : E → E} {G : Set E}
--       (hG : ∀ᵐ x ∂volume,x∈G) (hGd : ∀ x∈G,DifferentiableAt ℝ (gradient φ) x)
--       (hH : ∀ x∈G,(DeficitQuotient.hessian b φ x).IsHermitian)
--       (hlocal : ∀ c : E,∃ ell T Tm B K R : ℝ,0<ell ∧ 0≤T ∧ 0≤B ∧ 0≤K ∧ 0<R ∧
--         (∀ x∈G,x∈ball c R →
--           (A x-ell • (1:Mat)).PosSemidef ∧ (A x).trace≤T ∧ ‖A x‖≤Tm ∧ ‖β x‖≤B) ∧
--         (∀ x∈G,x∈ball c R → ∀ y∈G,y∈ball c R →
--           (A y*(DeficitQuotient.hessian b φ y-DeficitQuotient.hessian b φ x)).trace≤
--             K*(dist x c+dist y c)))
--       (hP : ∀ h : E,∀ᵐ x ∂volume,
--         ⟪β x,SecondDifference.vector (gradient φ) h x⟫_ℝ ≤
--           (A x*(DeficitQuotient.hessian b φ (x+h)+DeficitQuotient.hessian b φ (x-h)-
--             (2:ℝ) • DeficitQuotient.hessian b φ x)).trace+SecondDifference.scalar φ h x) :
--       ∃ M : E → Mat,Continuous M ∧ ∀ x∈G,M x=DeficitQuotient.hessian b φ x
--   ```
--
--   **Definitions.** The statement is written with `OAI.DeficitQuotient.hessian`, `OAI.SecondDifference.scalar` and `OAI.SecondDifference.vector` (definitions bundle `OAIW2LB000` of this split).
--
--   **Used by.** The proof of `OAI.LogBrunnMinkowski.softVariance` of this split imports it.
-- source:
--   OpenAI, The logarithmic Brunn–Minkowski conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 91; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-logarithmic-Brunn-Minkowski-conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/LogVolume/BrunnMinkowski.lean (declaration OAI.C11InteriorRegularity.continuous_hessian_rep)

import Mathlib
import Definitions.Def_OAIW2LB000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology NNReal

open Set Filter
open scoped Topology NNReal

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

open scoped ENNReal

open scoped InnerProductSpace ContDiff Topology
open scoped ENNReal

open Set MeasureTheory Filter
open scoped ENNReal Topology

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

open Set MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

open Set MeasureTheory Filter
open scoped InnerProductSpace Topology

noncomputable section

namespace C11InteriorRegularity
open Set Filter Metric Matrix MeasureTheory OscillationEnvelope FiniteElliptic
open scoped InnerProductSpace NNReal ENNReal Matrix.Norms.Elementwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "Mat" => Matrix ι ι ℝ
local notation "D" => ((Fintype.card ι:ℝ)/2+(2*(Fintype.card ι:ℝ)+1))

theorem continuous_hessian_rep (b : OrthonormalBasis ι ℝ E) {φ : E → ℝ} {L : ℝ≥0}
    (hd : Differentiable ℝ φ) (hL : LipschitzWith L (gradient φ))
    {A : E → Mat} {β : E → E} {G : Set E}
    (hG : ∀ᵐ x ∂volume,x∈G) (hGd : ∀ x∈G,DifferentiableAt ℝ (gradient φ) x)
    (hH : ∀ x∈G,(DeficitQuotient.hessian b φ x).IsHermitian)
    (hlocal : ∀ c : E,∃ ell T Tm B K R : ℝ,0<ell ∧ 0≤T ∧ 0≤B ∧ 0≤K ∧ 0<R ∧
      (∀ x∈G,x∈ball c R →
        (A x-ell • (1:Mat)).PosSemidef ∧ (A x).trace≤T ∧ ‖A x‖≤Tm ∧ ‖β x‖≤B) ∧
      (∀ x∈G,x∈ball c R → ∀ y∈G,y∈ball c R →
        (A y*(DeficitQuotient.hessian b φ y-DeficitQuotient.hessian b φ x)).trace≤
          K*(dist x c+dist y c)))
    (hP : ∀ h : E,∀ᵐ x ∂volume,
      ⟪β x,SecondDifference.vector (gradient φ) h x⟫_ℝ ≤
        (A x*(DeficitQuotient.hessian b φ (x+h)+DeficitQuotient.hessian b φ (x-h)-
          (2:ℝ) • DeficitQuotient.hessian b φ x)).trace+SecondDifference.scalar φ h x) :
    ∃ M : E → Mat,Continuous M ∧ ∀ x∈G,M x=DeficitQuotient.hessian b φ x := by
  sorry

end C11InteriorRegularity

end

end

end OAI
end
