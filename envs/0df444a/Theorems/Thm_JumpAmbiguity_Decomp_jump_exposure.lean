-- Prove2me | Theorems.Thm_JumpAmbiguity_Decomp_jump_exposure
-- name    : JumpAmbiguity.Decomp.jump_exposure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:20.512165+00:00
-- url     : https://prove2.me/theorems/ab6bbe97-952e-4bf3-8bef-9129fd5c3d01
-- title:
--   Appendix (A.6)–(A.7): jump exposure depends on the column-space component
-- statement:
--   For a portfolio $\pi$, write $\widehat\pi=\Sigma'\pi$ and decompose it as $\widehat\pi=\bar\pi+\pi_\perp$, where $\bar\pi$ is in the column space of $\widehat J=\Sigma^{-1}J$ and $\pi_\perp$ is orthogonal to that space. For every jump type $k$,
--
--   $$
--   \pi'J_k=\bar\pi'\widehat J_k.
--   $$
--
--   Thus the inner worst-case jump model, and the admissibility constraint for type $k$, depend on $\bar\pi$ alone. This is the exposure identity used in the proof of Proposition 2.
-- source:
--   Jin, Luo & Zeng, Tail Risk and Robust Portfolio Decisions, SSRN working paper 2865064 (version of April 18, 2017), p. 15 (PDF 16), paragraph after Proposition 2; p. 34 (PDF 35), (A.6)–(A.7)

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model

namespace JumpAmbiguity.Decomp

/-- The jump exposure identity used after (A.7) and stated on p. 15. -/
theorem jump_exposure {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (π : Fin m → ℝ) (k : Fin n) :
    π ⬝ᵥ M.col k = M.pibar π ⬝ᵥ M.Jhatcol k := by sorry

end JumpAmbiguity.Decomp
