-- Prove2me | Theorems.Thm_MemoSDPI_Main_theorem_6_4_rho_le_one
-- name    : MemoSDPI.Main.theorem_6_4_rho_le_one
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T16:22:18.467995+00:00
-- url     : https://prove2.me/theorems/b7e6c498-3ad6-456e-afc8-2502b2382cde
-- title:
--   Theorem 6.4 for ρ ≤ 1 (corrected: the printed statement has no bound on ρ)
-- statement:
--   **Source** (p. 26, Theorem 6.4): for a family $\mathcal P$, sets $\mathrm{Good}(D)$ and a $\rho$-replicable algorithm $A$ on $\mathcal P$ using $n$ samples with $\Pr[A(S;R)\in\mathrm{Good}(D)]\ge 1-\beta$ for every $D\in\mathcal P$, there is an algorithm $A'$ on $2n$ samples with $\Pr[A'(\tilde S)\in\mathrm{Good}(D)]\ge 1-\beta-\rho$ and $I(A'(\tilde S);\tilde S)\le\min\{3/e,\,2\rho+\rho\log(1/\rho)\}$ for every $D\in\mathcal P$, and $\mathrm{mem}_{2n}(A',P)\le\min\{3/e,\,2\rho+\rho\log(1/\rho)\}$ for every average-case problem over $\mathcal P$.
--
--   **Variant:** the same statement under the additional hypothesis $\rho\le 1$.
--
--   **Difference:** the hypothesis $\rho \le 1$ is added. Without it the statement is false for $\rho > e^2$, where every algorithm is $\rho$-replicable but the bound $2\rho+\rho\log(1/\rho)$ is negative. Every use in the paper has $\rho \le 1/100$.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 26, Theorem 6.4 (corrected)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_DPVerify_IsReplicableAt
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_MemoSDPI_Main_Memorization
import Definitions.Def_MemoSDPI_Main_IsReplicableOn
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MemoSDPI.Main

theorem theorem_6_4_rho_le_one {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (F : Set (ProbabilityMeasure X)) (Good : ProbabilityMeasure X → Set Y) (ρ β : ℝ)
    (hρ1 : ρ ≤ 1)
    (A : DPVerify.RandAlg X Y n) (hrep : IsReplicableOn A F ρ)
    (hsucc : ∀ D ∈ F, ENNReal.ofReal (1 - β) ≤
      ((Measure.pi fun _ : Fin n => (D : Measure X)).prod A.P) {q | A.run q.1 q.2 ∈ Good D}) :
    ∃ A' : DPVerify.RandAlg X (Y ⊕ Unit) (2 * n),
      (∀ D ∈ F,
        ENNReal.ofReal (1 - β - ρ) ≤
            ((Measure.pi fun _ : Fin (2 * n) => (D : Measure X)).prod A'.P)
              {q | ∃ y ∈ Good D, A'.run q.1 q.2 = Sum.inl y} ∧
          memD A' (D : Measure X) ≠ ∞ ∧
          (memD A' (D : Measure X)).toReal ≤
            min (3 / Real.exp 1) (2 * ρ + ρ * Real.log (1 / ρ))) ∧
      (∀ (Θ : Type) [MeasurableSpace Θ] (Ψ : Measure Θ) [IsProbabilityMeasure Ψ]
          (Pθ : Θ → ProbabilityMeasure X), (∀ᵐ θ ∂Ψ, Pθ θ ∈ F) →
        memAvg A' Ψ (fun θ => (Pθ θ : Measure X)) ≠ ∞ ∧
          (memAvg A' Ψ (fun θ => (Pθ θ : Measure X))).toReal ≤
            min (3 / Real.exp 1) (2 * ρ + ρ * Real.log (1 / ρ))) := by sorry

end MemoSDPI.Main
