-- Prove2me | Theorems.Thm_JumpAmbiguity_Decomp_separation_A8
-- name    : JumpAmbiguity.Decomp.separation_A8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:28.62525+00:00
-- url     : https://prove2.me/theorems/250cbaca-17ff-406b-9c49-64131feeffc1
-- title:
--   Equation (A.8): the robust generator separates by portfolio component
-- statement:
--   Under the market assumptions and jump-integrability condition, take an admissible portfolio $\pi$ and write $\Sigma'\pi=\bar\pi+\pi_\perp$ with $\bar\pi$ in the column space of $\widehat J$ and $\pi_\perp$ orthogonal to it. Let $G(\pi)$ be the pointwise robust generator of (A.1), including its actual inner infimum, and let $R$ be the reduced objective in (A.10). Then
--
--   $$
--   G(\pi)=r+\left(-\frac\gamma2\|\pi_\perp\|^2+\pi_\perp'\mu_\perp\right)+R(\bar\pi).
--   $$
--
--   The identity separates the unconstrained diffusion component from the jump-dependent reduced problem. It incorporates the worst-case entropy term in $R$.
--
--   **Formalization Note** The time-only derivative term in (A.1) is omitted from $G$ because it is independent of both the portfolio and the alternative model.
-- source:
--   Jin, Luo & Zeng, Tail Risk and Robust Portfolio Decisions, SSRN working paper 2865064 (version of April 18, 2017), p. 34 (PDF 35), (A.8), using (A.1)–(A.7)

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model

namespace JumpAmbiguity.Decomp

/-- The pointwise separation of the two portfolio components in (A.8). -/
theorem separation_A8 {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (π : Fin m → ℝ) (hπ : π ∈ M.Admissible) :
    M.generator π = M.r + M.diffusionObj (M.piperp π) + M.reducedObj (M.pibar π) := by sorry

end JumpAmbiguity.Decomp
