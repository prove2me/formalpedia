-- Prove2me | Theorems.Thm_JumpAmbiguity_Decomp_proposition_2
-- name    : JumpAmbiguity.Decomp.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:33.579419+00:00
-- url     : https://prove2.me/theorems/87e77484-d71b-4585-9a33-0fd49c7f0447
-- title:
--   Proposition 2: robust optimal portfolio decomposition
-- statement:
--   Consider the market of §2 under its standing assumptions and the integrability needed for the worst-case jump tilt. A portfolio $\pi$ maximizes the pointwise robust generator $G$ of (A.1) over all admissible portfolios if and only if there is an admissible reduced portfolio $\bar\pi$ in the column space of $\widehat J=\Sigma^{-1}J$ that maximizes the reduced objective $R$ of (A.10), such that
--
--   $$
--   \pi=(\Sigma')^{-1}\left(\bar\pi+\frac{\mu_\perp}{\gamma}\right),\qquad
--   \widehat\mu=\Sigma^{-1}(\mu-r\mathbf1)=\bar\mu+\mu_\perp.
--   $$
--
--   This characterizes the optimal portfolios: the diffusion exposure is explicit, while the jump exposure solves a lower-dimensional optimization problem. The result is an equivalence between maximizers and does not separately assert that a maximizer exists.
--
--   **Formalization Note** The paper solves the pointwise generator after the ansatz $V(W,t)=U(W)h(t)$ and does not give a stochastic verification theorem. The inner infimum over alternative jump models remains in $G$. The reduced objective follows the proof's (A.10), which includes the entropy term omitted from printed (17). It is optimized over the column space with the original jump-admissibility constraints. Integrability, $\gamma>0$ with $\gamma\ne1$, $\phi>0$, and $\lambda_k>0$ are explicit.
-- source:
--   Jin, Luo & Zeng, Tail Risk and Robust Portfolio Decisions, SSRN working paper 2865064 (version of April 18, 2017), p. 15 (PDF 16), Proposition 2, (16)–(17); proof p. 34 (PDF 35), (A.8)–(A.10)

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model

namespace JumpAmbiguity.Decomp

/-- Proposition 2, with the reduced objective from the proof's (A.10). -/
theorem proposition_2 {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (π : Fin m → ℝ) :
    (π ∈ M.Admissible ∧ ∀ π' ∈ M.Admissible, M.generator π' ≤ M.generator π) ↔
      ∃ pibar : Fin m → ℝ,
        (pibar ∈ M.ReducedAdmissible ∧
          ∀ x ∈ M.ReducedAdmissible, M.reducedObj x ≤ M.reducedObj pibar) ∧
        π = Matrix.mulVec ((M.Sig.transpose)⁻¹)
          (pibar + (1 / M.γ) • M.muperp) := by sorry

end JumpAmbiguity.Decomp
