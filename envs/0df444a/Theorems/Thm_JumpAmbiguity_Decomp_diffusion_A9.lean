-- Prove2me | Theorems.Thm_JumpAmbiguity_Decomp_diffusion_A9
-- name    : JumpAmbiguity.Decomp.diffusion_A9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:29.50682+00:00
-- url     : https://prove2.me/theorems/cc8e8ba7-95bd-4078-bccc-33bc5f4b84bf
-- title:
--   Equation (A.9): unique optimal diffusion exposure
-- statement:
--   Let $\mu_\perp$ be the part of the transformed excess return orthogonal to the column space of $\widehat J$. For positive risk aversion $\gamma$, the diffusion objective on that orthogonal space is
--
--   $$
--   D(x)=-\frac\gamma2 x'x+x'\mu_\perp.
--   $$
--
--   Its unique maximizer is $x=\mu_\perp/\gamma$. This gives the closed-form diffusion component $\pi_\perp^*$ in (A.9), independent of the jump-size laws and the ambiguity coefficient.
-- source:
--   Jin, Luo & Zeng, Tail Risk and Robust Portfolio Decisions, SSRN working paper 2865064 (version of April 18, 2017), p. 34 (PDF 35), (A.8)–(A.9)

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model

namespace JumpAmbiguity.Decomp

/-- Equation (A.9): the diffusion component has a unique quadratic maximizer. -/
theorem diffusion_A9 {m n : ℕ} (M : Market m n) (hS : M.Standing) :
    M.IsOrthogonalToK ((1 / M.γ) • M.muperp) ∧
    ∀ x : Fin m → ℝ, M.IsOrthogonalToK x →
      M.diffusionObj x ≤ M.diffusionObj ((1 / M.γ) • M.muperp) ∧
      (M.diffusionObj x = M.diffusionObj ((1 / M.γ) • M.muperp) →
        x = (1 / M.γ) • M.muperp) := by sorry

end JumpAmbiguity.Decomp
