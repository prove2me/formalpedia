-- Prove2me | Theorems.Thm_OTDRO_Statics_worst_case_comparative_statics
-- name    : OTDRO.Statics.worst_case_comparative_statics
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:15:22.307906+00:00
-- url     : https://prove2.me/theorems/31f46e28-7e64-44a6-a37a-91d297637bb4
-- title:
--   Theorem 7 — monotone worst-case displacements as δ increases
-- statement:
--   Suppose Assumptions 1–5 hold and fix $\beta\in B\setminus\{0\}$. There is $\delta_1\in(0,\delta_0)$ and a family $G_\delta$ such that, for every $0<\delta<\delta_1$, the law of
--
--   $$X^*_\delta=X+\sqrt\delta\,G_\delta(X)A(X)^{-1}\beta$$
--
--   is the unique distribution attaining the worst-case expected loss over the transport ball of radius $\delta$. For every $0<\delta<\delta'<\delta_1$, almost surely, $0<\sqrt\delta G_\delta<\sqrt{\delta'}G_{\delta'}$ where $\ell'(\beta^\top X)>0$, while $\sqrt{\delta'}G_{\delta'}<\sqrt\delta G_\delta<0$ where $\ell'(\beta^\top X)<0$. If the derivative is zero, $G_\delta=0$. Consequently,
--
--   $$\|X^*_\delta-X\|\le\|X^*_{\delta'}-X\|\quad\text{almost surely}.$$
--
--   Thus each observation moves along a fixed line, farther from its starting point as the ambiguity radius grows.
--
--   **Formalization Note** Assumption 5 is added because the proof invokes Theorem 4 to define $\delta_1$ and ensure a unique dual optimizer. The worst-case objective is the published coupling primal; the graph coupling is required to attain it and all optimal couplings must have the same second marginal. The almost-sure comparison is stated for each radius pair.
-- source:
--   arXiv:1810.02403v3, Theorem 7, p. 14; §5.4, proof, p. 41 (Assumption 5 addition)

import Mathlib
import Definitions.Def_OTDRO_Statics_Regions
import Definitions.Def_OTDRO_Statics_Transport

namespace OTDRO.Statics

open MeasureTheory

/-- Theorem 7, p. 14: as the ambiguity radius grows, each worst-case displacement
moves monotonically along its line from the original point. -/
theorem worst_case_comparative_statics {d : ℕ}
    (P0 : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hB4 : OTDRO.StrongCvx.Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (h5 : OTDRO.StrongCvx.Assumption5 P0 ℓ B)
    (Llow Lbar : ℝ)
    (hL : 0 < Llow ∧ ∀ β ∈ B,
      Llow ≤ ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ∧
      ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ≤ Lbar)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0) :
    ∃ δ1 : ℝ, 0 < δ1 ∧ δ1 < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (Rβ B) M ∧
      ∃ G : ℝ → EuclideanSpace ℝ (Fin d) → ℝ,
        (∀ δ ∈ Set.Ioo 0 δ1,
          AEMeasurable (G δ) P0 ∧
          AEMeasurable (shiftMap A δ β (G δ)) P0 ∧
          OTDRO.WorstCase.graphCoupling P0 (shiftMap A δ β (G δ)) ∈
            ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ ∧
          ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x))
            (OTDRO.WorstCase.graphCoupling P0 (shiftMap A δ β (G δ))) =
            ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
              (fun x => ℓ (inner ℝ β x)) P0 δ ∧
          ∀ π ∈ ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ,
            ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) π =
              ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
                (fun x => ℓ (inner ℝ β x)) P0 δ →
            π.map Prod.snd = P0.map (shiftMap A δ β (G δ))) ∧
        (∀ δ δ' : ℝ, 0 < δ → δ < δ' → δ' < δ1 →
          ∀ᵐ x ∂P0,
            (0 < deriv ℓ (inner ℝ β x) →
              0 < Real.sqrt δ * G δ x ∧
              Real.sqrt δ * G δ x < Real.sqrt δ' * G δ' x) ∧
            (deriv ℓ (inner ℝ β x) < 0 →
              Real.sqrt δ' * G δ' x < Real.sqrt δ * G δ x ∧
              Real.sqrt δ * G δ x < 0) ∧
            ‖shiftMap A δ β (G δ) x - x‖ ≤
              ‖shiftMap A δ' β (G δ') x - x‖) ∧
        (∀ δ ∈ Set.Ioo 0 δ1,
          ∀ᵐ x ∂P0,
            deriv ℓ (inner ℝ β x) = 0 → G δ x = 0) := by sorry

end OTDRO.Statics
