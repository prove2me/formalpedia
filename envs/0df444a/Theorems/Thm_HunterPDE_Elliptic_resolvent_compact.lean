-- Prove2me | Theorems.Thm_HunterPDE_Elliptic_resolvent_compact
-- name    : HunterPDE.Elliptic.resolvent_compact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T23:51:20.406993+00:00
-- url     : https://prove2.me/theorems/6f5c98e8-9587-49fb-b921-06ff8eea9343
-- title:
--   Theorem 4.23 — the resolvent K = (L + μI)⁻¹ on L²(Ω): adjoint K* and compactness on bounded Ω
-- statement:
--   Let $L$ be as in Theorem 4.22, $\gamma$ a constant for which Theorem 4.21 holds, and $\mu \ge \gamma$. Define $K : L^2(\Omega) \to L^2(\Omega)$ by (4.26): $Kf = u$ iff $u \in H^1_0(\Omega)$ and
--   $$a(u,v) + \mu(u,v)_{L^2} = (f,v)_{L^2} \qquad \text{for all } v \in H^1_0(\Omega),$$
--   and $K^*$ by (4.27) with $a$ replaced by the adjoint form $a^*$. Then $K$ is a bounded linear operator on $L^2(\Omega)$ whose Hilbert-space adjoint is $K^*$, and if $\Omega$ is a bounded open set then $K$ is compact.
--
--   Compactness of the resolvent is what turns the elliptic problem into a compact-perturbation-of-the-identity problem, to which the Fredholm alternative applies.
--
--   **Formalization Note.** $K$ and $K^*$ are the functions `resolvent Ω P μ` and `resolventAdj Ω P μ`; the theorem asserts that `resolvent` is a continuous linear map `K`, that `ContinuousLinearMap.adjoint K` is `resolventAdj`, and that `K` is an `IsCompactOperator` when `Ω` is bounded.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 106, Theorem 4.23

import Mathlib
import Definitions.Def_HunterPDE_Elliptic_EllipticOperator

open MeasureTheory

namespace HunterPDE.Elliptic

/-- Theorem 4.23 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 106: for `μ ≥ γ`, `γ` a
constant for which Theorem 4.21 holds, the resolvent `K = (L + μI)⁻¹|_{L²(Ω)}` of (4.26)
(`K f = u` iff `a_μ(u, v) = (f, v)_{L²}` for all `v ∈ H¹₀(Ω)`) is a bounded linear operator on
`L²(Ω)`, its adjoint is the operator `K* = (L* + μI)⁻¹|_{L²(Ω)}` of (4.27), and if `Ω` is a
bounded open set then `K` is compact. -/
theorem resolvent_compact {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (P : Coeffs n) (hP : P.Admissible Ω) (γ : ℝ)
    (hγ : ∃ C₁ : ℝ, 0 < C₁ ∧ ∃ C₂ : ℝ, 0 < C₂ ∧
      (∀ u : H10 n Ω, C₁ * ‖u‖ ^ 2 ≤ form P u u + γ * l2inner u u) ∧
      ∀ u v : H10 n Ω, |form P u v| ≤ C₂ * ‖u‖ * ‖v‖)
    (μ : ℝ) (hμ : γ ≤ μ) :
    ∃ K : Lp ℝ 2 (volume.restrict Ω) →L[ℝ] Lp ℝ 2 (volume.restrict Ω),
      ⇑K = resolvent Ω P μ ∧ ⇑(ContinuousLinearMap.adjoint K) = resolventAdj Ω P μ ∧
      (Bornology.IsBounded Ω → IsCompactOperator K) := by sorry

end HunterPDE.Elliptic
