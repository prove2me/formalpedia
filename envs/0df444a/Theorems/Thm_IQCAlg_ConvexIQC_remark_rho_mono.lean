-- Prove2me | Theorems.Thm_IQCAlg_ConvexIQC_remark_rho_mono
-- name    : IQCAlg.ConvexIQC.remark_rho_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:57.803595+00:00
-- url     : https://prove2.me/theorems/2fa179b7-8185-4acf-b404-0509c224c121
-- title:
--   Remark after Theorem 4, item 3, p. 11 — a ρ₁-hard IQC is ρ-hard for every ρ ≥ ρ₁
-- statement:
--   Let $(w_t)_{t\ge0}$ be real numbers and $0<\rho_1\le\rho$. If
--   $$\sum_{t=0}^{k}\rho_1^{-2t}\,w_t\ \ge\ 0\qquad\text{for all }k\ge0,$$
--   then
--   $$\sum_{t=0}^{k}\rho^{-2t}\,w_t\ \ge\ 0\qquad\text{for all }k\ge0 .$$
--
--   With $w_t=(z_t-z_\star)^{\mathsf T}M(z_t-z_\star)$ this is the first sentence of item 3 of the remarks after Theorem 4: if a $\rho_1$-hard IQC is satisfied, then so is the $\rho$-hard IQC for any $\rho\ge\rho_1$. The proof of Lemma 10 uses it to pass from $\bar\rho$ to $\rho$.
--
--   **Formalization Note** The remark is stated for the scalar summand $w_t$, since its content does not depend on $\Psi$ or $M$. The weight $\rho^{-2t}$ is written $(\rho^{2t})^{-1}$; $\rho_1>0$ is required because $\rho_1^{-2t}$ is undefined at $\rho_1=0$ (in Lean $0^{-1}=0$).
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 11, remarks after Theorem 4 (Pointwise and hard IQCs), item 3, first sentence

import Mathlib
import Definitions.Def_IQCAlg_ConvexIQC_Setting

open scoped InnerProductSpace

namespace IQCAlg.ConvexIQC

/-- Remark after Theorem 4, item 3, first sentence, p. 11: a `ρ₁`-hard IQC is `ρ`-hard for
every `ρ ≥ ρ₁`, stated for the scalar summand `w t = (z_t − z⋆)ᵀM(z_t − z⋆)`. -/
theorem remark_rho_mono (w : ℕ → ℝ) (ρ₁ ρ : ℝ) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ ≤ ρ)
    (hw : ∀ k : ℕ, 0 ≤ ∑ t ∈ Finset.range (k + 1), (ρ₁ ^ (2 * t))⁻¹ * w t) :
    ∀ k : ℕ, 0 ≤ ∑ t ∈ Finset.range (k + 1), (ρ ^ (2 * t))⁻¹ * w t := by sorry

end IQCAlg.ConvexIQC
