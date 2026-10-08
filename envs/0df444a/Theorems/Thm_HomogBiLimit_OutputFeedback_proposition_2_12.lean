-- Prove2me | Theorems.Thm_HomogBiLimit_OutputFeedback_proposition_2_12
-- name    : HomogBiLimit.OutputFeedback.proposition_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:45.033323+00:00
-- url     : https://prove2.me/theorems/f7deb325-c53d-4c75-b23c-846073dbf5b9
-- title:
--   Proposition 2.12 — integral of a function homogeneous in the 0-limit or the ∞-limit
-- statement:
--   Let $\phi:\mathbb R^n\to\mathbb R$ and fix a coordinate $i$. Define
--   $$\Phi_i(x)=\int_0^{x_i}\phi(x_1,\dots,x_{i-1},s,x_{i+1},\dots,x_n)\,ds .$$
--   1. If $\phi$ is homogeneous in the 0-limit with triple $(r_0,d_0,\phi_0)$, then $\Phi_i$ is homogeneous in the 0-limit with triple $(r_0,\ d_0+r_{0,i},\ \Phi_{i,0})$, where $\Phi_{i,0}$ is the same integral with $\phi_0$ in place of $\phi$.
--   2. If $\phi$ is homogeneous in the ∞-limit with triple $(r_\infty,d_\infty,\phi_\infty)$, then $\Phi_i$ is homogeneous in the ∞-limit with triple $(r_\infty,\ d_\infty+r_{\infty,i},\ \Phi_{i,\infty})$.
--
--   Integration along one coordinate raises the degree by that coordinate's weight; the paper uses this to build Lyapunov functions recursively.
--
--   **Formalization Note** The integral is the oriented interval integral $\int_0^{x_i}$, and the integrand is $\phi$ at $x$ with its $i$-th coordinate replaced by $s$ (`Function.update`). Coordinates are indexed from 0 in Lean.
-- source:
--   Andrieu, Praly, Astolfi, Homogeneous Approximation, Recursive Observer Design, and Output Feedback, arXiv:0903.0298v1, pp. 5–6, Proposition 2.12

import Mathlib
import Definitions.Def_HomogBiLimit_OutputFeedback_Homogeneity
import Definitions.Def_HomogBiLimit_OutputFeedback_ChainSystems

namespace HomogBiLimit.OutputFeedback

/-- Proposition 2.12 (integral function), pp. 5–6: if `φ` is homogeneous in the 0-limit
(resp. ∞-limit) with triple `(r, d, φ₀)`, then `Φᵢ(x) = ∫₀^{xᵢ} φ(x₁,…,x_{i−1}, s, x_{i+1},…,xₙ) ds`
is homogeneous in the 0-limit (resp. ∞-limit) with triple `(r, d + rᵢ, Φ_{i,0})`, where
`Φ_{i,0}` is the same integral of `φ₀`. -/
theorem proposition_2_12 {n : ℕ} (φ φ₀ φinf : (Fin n → ℝ) → ℝ) (i : Fin n) :
    (∀ (r₀ : Fin n → ℝ) (d₀ : ℝ), IsHomogZero φ r₀ d₀ φ₀ →
      IsHomogZero (fun x => ∫ s in (0 : ℝ)..x i, φ (Function.update x i s)) r₀ (d₀ + r₀ i)
        (fun x => ∫ s in (0 : ℝ)..x i, φ₀ (Function.update x i s))) ∧
    (∀ (rinf : Fin n → ℝ) (dinf : ℝ), IsHomogInfty φ rinf dinf φinf →
      IsHomogInfty (fun x => ∫ s in (0 : ℝ)..x i, φ (Function.update x i s)) rinf
        (dinf + rinf i)
        (fun x => ∫ s in (0 : ℝ)..x i, φinf (Function.update x i s))) := by sorry

end HomogBiLimit.OutputFeedback
