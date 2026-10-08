-- Prove2me | Theorems.Thm_OTDRO_Statics_worst_case_unique_monge
-- name    : OTDRO.Statics.worst_case_unique_monge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:14:18.247221+00:00
-- url     : https://prove2.me/theorems/4bb2e2fe-9763-43c9-9573-e769c2e87956
-- title:
--   Theorem 6(e) — unique worst-case law from a deterministic transport
-- statement:
--   Suppose Assumptions 1–3 hold, $\delta>0$, $\beta\in B\setminus\{0\}$, and $\lambda_*$ minimizes $f_\delta(\beta,\lambda)$ over $\lambda\ge0$, with $\lambda_*>\lambda'_{\rm thr}(\beta)$. The scalar maximizer is unique $P_0$-almost surely. If $G(x)$ is that maximizer, the graph coupling of
--
--   $$X^*=X+\sqrt\delta\,G(X)A(X)^{-1}\beta$$
--
--   is primal feasible, attains the worst-case value, and spends exactly $\delta$ in expected transport cost. Every optimal feasible coupling has the same second marginal, so the law of $X^*$ is the unique worst-case distribution.
--
--   This result supplies the primal identification used in Theorem 7.
--
--   **Formalization Note** The singleton assertion is almost sure rather than the printed “for every $x$”: the essential-supremum threshold controls $A(x)$ only on a full-measure set. Measurability of $G$ and the transport map are conclusions.
-- source:
--   arXiv:1810.02403v3, Theorem 6(e), p. 14 (almost-sure correction)

import Mathlib
import Definitions.Def_OTDRO_Statics_Assumptions
import Definitions.Def_OTDRO_Statics_Transport

namespace OTDRO.Statics

open MeasureTheory

/-- Theorem 6(e), p. 14, with the singleton claim on a P₀-full set. -/
theorem worst_case_unique_monge {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (β : EuclideanSpace ℝ (Fin d)) (hβB : β ∈ B) (hβ : β ≠ 0)
    (lamStar : ℝ) (hlam : 0 ≤ lamStar)
    (hmin : IsMinOn (fun lam => OTDRO.Dual.fDelta P0 ℓ A δ β lam) (Set.Ici 0) lamStar)
    (hthr : OTDRO.Dual.lamThr' P0 A M δ β < lamStar) :
    ∃ G : EuclideanSpace ℝ (Fin d) → ℝ,
      AEMeasurable G P0 ∧
      AEMeasurable (shiftMap A δ β G) P0 ∧
      (∀ᵐ x ∂P0, OTDRO.Dual.maximizers ℓ A δ β lamStar x = {G x}) ∧
      OTDRO.WorstCase.graphCoupling P0 (shiftMap A δ β G) ∈
        ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ ∧
      ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x))
        (OTDRO.WorstCase.graphCoupling P0 (shiftMap A δ β G)) =
        ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
          (fun x => ℓ (inner ℝ β x)) P0 δ ∧
      (∀ π ∈ ModelRiskOT.Duality.primalFeasible (OTDRO.Dual.mahalCost A) P0 δ,
        ModelRiskOT.Duality.primalObj (fun x => ℓ (inner ℝ β x)) π =
          ModelRiskOT.Duality.primalValue (OTDRO.Dual.mahalCost A)
            (fun x => ℓ (inner ℝ β x)) P0 δ →
        π.map Prod.snd = P0.map (shiftMap A δ β G)) ∧
      (∫⁻ p, ENNReal.ofReal (OTDRO.Dual.mahalCost A p.1 p.2)
          ∂(OTDRO.WorstCase.graphCoupling P0 (shiftMap A δ β G))) = ENNReal.ofReal δ := by sorry

end OTDRO.Statics
