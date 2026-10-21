-- Prove2me | Theorems.Thm_NetworkVolatility_Robust_lamMax_eq_norm_of_symm
-- name    : NetworkVolatility.Robust.lamMax_eq_norm_of_symm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:18:19.220982+00:00
-- url     : https://prove2.me/theorems/385f1e03-58a5-4e1f-b04b-a8d75fc3864c
-- title:
--   Proof of Theorem 1, Part 1, p. 12 — for symmetric $M$, $\lambda_{\max}(M)=\rho(M)=\|M\|_2$
-- statement:
--   Let $M$ be a real symmetric $n\times n$ matrix. Then its spectral norm, its spectral radius and its largest absolute eigenvalue coincide:
--   $$\lambda_{\max}(M)=\|M\|_2\qquad\text{and}\qquad\rho(M)=\|M\|_2 .$$
--
--   The proof of Theorem 1 uses this fact (stated in a parenthesis on p. 12: "the norm 2 and spectral radius of any symmetric matrix are equal") to pass between the perturbation bound of Definition 2, which is in the spectral norm, and the eigenvalue $\lambda_{\max}$ in the formula of Theorem 1.
--
--   **Formalization Note** $\lambda_{\max}(M)$ is the largest $|\mu|$ over real eigenvalues $\mu$ of $M$, and $\rho(M)$ the largest modulus over complex eigenvalues; both are $0$ for $n=0$, as is the norm.
-- source:
--   Baron, Hu & Malekian, Revenue volatility under uncertain network effects, SSRN preprint 3561270 (version of 2020-03-25), p. 12, proof of Theorem 1, Part 1

import Mathlib
import Definitions.Def_NetworkVolatility_Robust_Model

namespace NetworkVolatility.Robust

open scoped Matrix.Norms.L2Operator

/-- Proof of Theorem 1, Part 1, p. 12: for a symmetric real matrix `M`, the spectral norm `‖M‖₂`,
the spectral radius `ρ(M)` and `λmax(M)` (the largest absolute value of an eigenvalue) coincide. -/
theorem lamMax_eq_norm_of_symm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    lamMax M = ‖M‖ ∧ specRadius M = ‖M‖ := by sorry

end NetworkVolatility.Robust
