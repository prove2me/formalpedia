-- Prove2me | Theorems.Thm_JumpAmbiguity_Decomp_decomposition_15
-- name    : JumpAmbiguity.Decomp.decomposition_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:15.82775+00:00
-- url     : https://prove2.me/theorems/e393bf43-9980-4a99-9307-f0384c206ab6
-- title:
--   Equation (15): unique orthogonal decomposition and matrix projection
-- statement:
--   Let $\widehat J=\Sigma^{-1}J$ have full column rank, and let $K$ be its column space. The Gram matrix $\widehat J'\widehat J$ is invertible. Every vector $v\in\mathbb R^m$ has a unique decomposition $v=\bar v+v_\perp$ with $\bar v\in K$ and $v_\perp\perp K$, where
--
--   $$
--   \bar v=\widehat J(\widehat J'\widehat J)^{-1}\widehat J'v,\qquad v_\perp=v-\bar v.
--   $$
--
--   Applying this result to $v=\widehat\mu$ gives the paper's $\widehat\mu=\bar\mu+\mu_\perp$ and its displayed formula for $\bar\mu$. The decomposition is the linear-algebraic basis for separating jump exposure from diffusion exposure.
--
--   **Formalization Note** Vectors are functions $\operatorname{Fin}(m)\to\mathbb R$, and orthogonality is their usual dot product. The paper constructs a basis $\widehat J_\perp$ when $m>n$; the statement uses its intrinsic orthogonal subspace, which also covers $m=n$ and $n=0$.
-- source:
--   Jin, Luo & Zeng, Tail Risk and Robust Portfolio Decisions, SSRN working paper 2865064 (version of April 18, 2017), p. 14 (PDF 15), (14)–(15) and following paragraph

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model

namespace JumpAmbiguity.Decomp

/-- Equation (15) and its stated uniqueness, with the displayed matrix projection. -/
theorem decomposition_15 {m n : ℕ} (M : Market m n) (hS : M.Standing) :
    IsUnit (M.Jhat.transpose * M.Jhat).det ∧
    ∀ v : Fin m → ℝ,
      M.proj v ∈ M.K ∧ M.IsOrthogonalToK (v - M.proj v) ∧
      v = M.proj v + (v - M.proj v) ∧
      ∀ x y : Fin m → ℝ,
        x ∈ M.K → M.IsOrthogonalToK y → v = x + y →
          x = M.proj v ∧ y = v - M.proj v := by sorry

end JumpAmbiguity.Decomp
