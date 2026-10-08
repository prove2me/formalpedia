-- Prove2me | Theorems.Thm_OffloadGNEP_Mono_jacobian_psd_of_Bs_psd
-- name    : OffloadGNEP.Mono.jacobian_psd_of_Bs_psd
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:37.747159+00:00
-- url     : https://prove2.me/theorems/e9b5e412-0caf-44d5-91b8-a22685580d05
-- title:
--   Proof of Theorem 1, p. 12 — on K, JF(x) is positive semidefinite as soon as Bˢ = ½(Bᵀ + B) is
-- statement:
--   Assume Assumption A and the standing hypotheses, and let $x\in K$. Let $B$ be the $N\times N$ matrix with diagonal entries $B_u$ and off-diagonal entries $B_{uv}$ from (17), and $B^s=\frac12(B^\top+B)$ its symmetric part. If $B^s$ is positive semidefinite, then the Jacobian $JF(x)$ of (16) is positive semidefinite as a quadratic form:
--   $$h^\top JF(x)\,h\ \ge\ 0\qquad\text{for all }h\in\mathbb R^{3N}.$$
--
--   After reordering the variables $JF(x)=\mathrm{diag}(A,B,0)$ with $A=\mathrm{diag}(A_u)$, and $A$ is positive definite under Assumption A; this is the step that reduces the monotonicity of $F$ to the semidefiniteness of $B^s$.
--
--   **Formalization Note** $JF(x)$ is not symmetric, so "positive semidefinite" for it means nonnegativity of the quadratic form $\sum_{p}h_p(JF(x)h)_p$ over the index set (user, tier). For the symmetric $B^s$ it is Mathlib's `Matrix.PosSemidef`.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 12, proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_OffloadGNEP_Mono_Setting

namespace OffloadGNEP.Mono

theorem jacobian_psd_of_Bs_psd {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (x : Fin N → Tier → ℝ) (hx : x ∈ K P) (hB : (Bs P x).PosSemidef) :
    ∀ h : Fin N × Tier → ℝ, 0 ≤ ∑ p, h p * Matrix.mulVec (JF P x) h p := by sorry

end OffloadGNEP.Mono
