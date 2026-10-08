-- Prove2me | Theorems.Thm_OTDRO_Statics_prop9_b
-- name    : OTDRO.Statics.prop9_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:46.239278+00:00
-- url     : https://prove2.me/theorems/0d7df4de-cc7e-416e-8d37-0b09e9d44ab6
-- title:
--   Proposition 9(b) — unique scalar maximizer and bounds (33)
-- statement:
--   Under Assumptions 1–4 and $0<\delta<\delta_0$, for every nonzero $\beta\in B$ and $(\beta,\lambda)\in\mathbb W$, the scalar maximizer $g(\beta,\lambda;x)$ is unique for $P_0$-almost every $x$. Writing
--
--   $$\varphi_g=2\lambda-\sqrt\delta\,\beta^\top A(x)^{-1}\beta\,\ell''\bigl(\beta^\top x+\sqrt\delta\,g\,\beta^\top A(x)^{-1}\beta\bigr),$$
--
--   it satisfies $\varphi_g\ge\varphi_{\min}\|\beta\|$ and $|g|\le|\ell'(\beta^\top x)|/(\varphi_{\min}\|\beta\|)$. On $\mathbb V$ it also satisfies the lower bound $|g|\ge|\ell'(\beta^\top x)|/(2K_2\|\beta\|)$.
--
--   The bounds constrain the response of the worst-case displacement to a change in the ambiguity radius.
--
--   **Formalization Note** The paper prints a strict $\varphi_g$ lower bound, but its proof gives only $\ge$ and equality occurs for a quadratic loss at the boundary of $\mathbb W$. A single scalar field indexed by the dual parameters represents the unique maximizers; its restriction to $\mathcal U$ is measurable and its sections on $\mathbb W$ are almost-everywhere measurable.
-- source:
--   arXiv:1810.02403v3, Proposition 9(b), (33), p. 37 (non-strict correction)

import Mathlib
import Definitions.Def_OTDRO_Statics_Regions

namespace OTDRO.Statics

open MeasureTheory

/-- Proposition 9(b), p. 37: the selected maximizer in W is unique and obeys (33).
The paper's strict φ lower bound is corrected to a non-strict one. -/
theorem prop9_b {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P0]
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (ρmin ρmax : ℝ) (hA : OTDRO.Dual.Assumption1 P0 A ρmin ρmax)
    (ℓ : ℝ → ℝ) (h2 : OTDRO.Dual.Assumption2 P0 ℓ)
    (δ : ℝ) (hδ : 0 < δ)
    (B : Set (EuclideanSpace ℝ (Fin d))) (hB : Convex ℝ B)
    (hB4 : OTDRO.StrongCvx.Assumption4 B) (hBne : B.Nonempty)
    (M : ℝ) (h3 : OTDRO.StrongCvx.Assumption3 P0 ℓ B M)
    (Llow Lbar : ℝ)
    (hL : 0 < Llow ∧ ∀ β ∈ B,
      Llow ≤ ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ∧
      ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ≤ Lbar)
    (hsmall : δ < OTDRO.StrongCvx.delta0 ρmin ρmax Llow (Rβ B) M) :
    ∃ g : (EuclideanSpace ℝ (Fin d) × ℝ) →
        EuclideanSpace ℝ (Fin d) → ℝ,
      Measurable (fun p : {p : (EuclideanSpace ℝ (Fin d) × ℝ) ×
          EuclideanSpace ℝ (Fin d) //
          p.1 ∈ regionU P0 ℓ A δ B p.2} => g p.1.1 p.1.2) ∧
      ∀ β ∈ B, β ≠ 0 → ∀ lam : ℝ,
        (β, lam) ∈ OTDRO.StrongCvx.regionW B δ M (Rβ B) ρmin ρmax Llow Lbar →
        AEMeasurable (g (β, lam)) P0 ∧
        ∀ᵐ x ∂P0, OTDRO.Dual.maximizers ℓ A δ β lam x = {g (β, lam) x} ∧
          OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin * ‖β‖ ≤
            2 * lam - Real.sqrt δ * OTDRO.Dual.quadInv A β x *
              deriv (deriv ℓ) (inner ℝ β x +
                Real.sqrt δ * g (β, lam) x * OTDRO.Dual.quadInv A β x) ∧
          |g (β, lam) x| ≤ |deriv ℓ (inner ℝ β x)| /
            (OTDRO.StrongCvx.phiMin δ Llow ρmax (Rβ B) M ρmin * ‖β‖) ∧
          ((β, lam) ∈ OTDRO.StrongCvx.regionV B δ M (Rβ B) ρmin ρmax Llow Lbar →
            |deriv ℓ (inner ℝ β x)| /
              (2 * OTDRO.StrongCvx.K2 δ M (Rβ B) ρmin Lbar * ‖β‖) ≤ |g (β, lam) x|) := by sorry

end OTDRO.Statics
