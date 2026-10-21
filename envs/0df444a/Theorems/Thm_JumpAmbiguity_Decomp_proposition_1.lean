-- Prove2me | Theorems.Thm_JumpAmbiguity_Decomp_proposition_1
-- name    : JumpAmbiguity.Decomp.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:43:08.745288+00:00
-- url     : https://prove2.me/theorems/909f64fd-c247-4e6f-982a-6bc06b72ec2d
-- title:
--   Proposition 1: exponential worst-case jump tilt
-- statement:
--   Let the jump market satisfy the standing assumptions, and let the worst-case tilt and its product with the CRRA jump increment be integrable. Fix a jump type $k$ and an admissible jump exposure $a\in[0,1]$. Define
--
--   $$
--   \psi_k^*(a,y)=\exp\!\left(\frac{\phi}{\gamma-1}\big((1+ay)^{1-\gamma}-1\big)\right),\qquad
--   \vartheta_k^*(a)=\int\psi_k^*(a,y)\,d\Phi_k(y),\qquad
--   \varphi_k^*(a,y)=\frac{\psi_k^*(a,y)}{\vartheta_k^*(a)}.
--   $$
--
--   Then $(\vartheta_k^*,\varphi_k^*)$ is an admissible intensity-and-density pair and attains the minimum of the entropy-penalized inner objective $L_k(a,\vartheta,\varphi)$ over all admissible pairs. Every admissible minimizing pair has the same intensity and the same density $\Phi_k$-almost everywhere. This identifies the worst-case model used in the portfolio decomposition.
--
--   **Formalization Note** The paper writes the claim for every admissible portfolio $\pi$; its inner problem depends on $\pi$ only through $a=\pi'J_k$. The explicit integrability condition makes the real-valued factors and objective meaningful.
-- source:
--   Jin, Luo & Zeng, Tail Risk and Robust Portfolio Decisions, SSRN working paper 2865064 (version of April 18, 2017), p. 12 (PDF 13), Proposition 1, (10)–(11); proof pp. 33–34 (PDF 34–35), (A.1)–(A.5)

import Mathlib
import Definitions.Def_JumpAmbiguity_Decomp_Model

namespace JumpAmbiguity.Decomp

/-- Proposition 1, equations (10)–(11): the tilted jump law is the solution of the inner problem. -/
theorem proposition_1 {m n : ℕ} (M : Market m n) (hS : M.Standing)
    (hI : M.JumpIntegrable) (k : Fin n) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    M.AdmissiblePair k a (M.thetaStar k a) (M.varphiStar k a) ∧
      IsLeast {v : ℝ | ∃ θ varphi, M.AdmissiblePair k a θ varphi ∧
        v = M.innerObj k a θ varphi}
        (M.innerObj k a (M.thetaStar k a) (M.varphiStar k a)) ∧
      ∀ θ (varphi : ℝ → ℝ), M.AdmissiblePair k a θ varphi →
        M.innerObj k a θ varphi = M.innerObj k a (M.thetaStar k a) (M.varphiStar k a) →
          θ = M.thetaStar k a ∧ varphi =ᵐ[M.Phi k] M.varphiStar k a := by sorry

end JumpAmbiguity.Decomp
