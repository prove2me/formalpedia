-- Prove2me | Theorems.Thm_NonconvexDRS_DRS_prop_3_2
-- name    : NonconvexDRS.DRS.prop_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:00.773513+00:00
-- url     : https://prove2.me/theorems/65e67534-f03e-408f-af60-ac0ce32b587d
-- title:
--   Proposition 3.2, p. 9 — under Assumption I, for γ < 1/L the Douglas–Rachford envelope is real-valued and strictly continuous
-- statement:
--   Suppose Assumption I holds: $\varphi_1:\mathbb R^p\to\mathbb R$ is $L$-smooth and $\sigma$-hypoconvex with $\sigma\in[-L,L]$, $\varphi_2:\mathbb R^p\to\overline{\mathbb R}$ is proper and lower semicontinuous, and $\varphi=\varphi_1+\varphi_2$ has a minimizer. Then for every $0<\gamma<1/L$ the Douglas–Rachford envelope $\varphi^{\mathrm{DR}}_\gamma$ takes only real values and is strictly continuous (locally Lipschitz):
--   $$\varphi^{\mathrm{DR}}_\gamma:\mathbb R^p\to\mathbb R\ \text{ is locally Lipschitz.}$$
--
--   Continuity of the envelope is what lets cluster points of DRS inherit the limit value of $\varphi^{\mathrm{DR}}_\gamma(s^k)$ in Theorem 4.3.
--
--   **Formalization Note** Real-valuedness is the existence of a real function $F$ with $\varphi^{\mathrm{DR}}_\gamma=F$ as `EReal` functions; strict continuity in the sense of Rockafellar–Wets is `LocallyLipschitz F`. The added hypothesis $L>0$ is the standing convention of this mission (Theorem 4.1 uses $p=\sigma/L$); for $L=0$, $\varphi_1$ is affine. $\gamma<1/L$ is written $\gamma L<1$.
-- source:
--   Themelis & Patrinos, Douglas-Rachford splitting and ADMM for nonconvex optimization: tight convergence results, arXiv:1709.05747v4, p. 9, Proposition 3.2

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_DRS_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace NonconvexDRS.DRS

/-- Proposition 3.2 (Strict continuity), p. 9. -/
theorem prop_3_2 {p : ℕ} (φ₁ : EuclideanSpace ℝ (Fin p) → ℝ) (φ₂ : EuclideanSpace ℝ (Fin p) → EReal)
    (L σ : ℝ) (hL : 0 < L) (hσ : -L ≤ σ ∧ σ ≤ L)
    (hsmooth : IsLSmooth φ₁ L) (hhypo : IsHypoconvex φ₁ σ)
    (hprop : IsProper φ₂) (hlsc : LowerSemicontinuous φ₂)
    (hsol : ∃ xs, ∀ x, (φ₁ xs : EReal) + φ₂ xs ≤ (φ₁ x : EReal) + φ₂ x)
    (γ : ℝ) (hγ : 0 < γ) (hγL : γ * L < 1) :
    ∃ F : EuclideanSpace ℝ (Fin p) → ℝ, LocallyLipschitz F ∧
      ∀ s, dre φ₁ φ₂ γ s = (F s : EReal) := by sorry

end NonconvexDRS.DRS
