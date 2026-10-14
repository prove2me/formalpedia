-- Prove2me | Theorems.Thm_GPhNGIDiffusion_EMError_lyapunov_A4_A7
-- name    : GPhNGIDiffusion.EMError.lyapunov_A4_A7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:32.760366+00:00
-- url     : https://prove2.me/theorems/3a91e787-cc23-4ee2-a005-f7f463b29c94
-- title:
--   (A.4)–(A.7): $V=(e'y)^2+\kappa[y-p\phi(e'y)]'\tilde Q[y-p\phi(e'y)]+\hat c_2$ satisfies $\mathcal AV\le -c_1V+\breve c_1$
-- statement:
--   Consider the limiting diffusion with drift $g$ and generator $\mathcal A$ of a model, and let $R=(I-P')\mathrm{diag}(v)$. There exist a positive definite matrix $\tilde Q$ with $\sum_{i,j}|\tilde Q_{ij}|=1$ such that
--   $$
--   \tilde Q(-R)+(-R)'\tilde Q<0,\qquad \tilde Q(-(I-pe')R)+(-R'(I-ep'))\tilde Q\le 0,
--   $$
--   and constants $\kappa>0$, $\hat c_2>0$, $c_1>0$, $\breve c_1>0$ such that the function
--   $$
--   V(y)=(e'y)^2+\kappa\,[y-p\phi(e'y)]'\tilde Q\,[y-p\phi(e'y)]+\hat c_2
--   $$
--   is a Lyapunov function of the model with constants $c_1,\breve c_1$: $V\in C^2(\mathbb R^d,\mathbb R_+)$, $\hat c_1|y|^2\le V(y)\le \hat C|y|^2+\hat C'$ (A.5), $|\nabla V(y)|\le C(1+|y|)$ (A.6), and
--   $$
--   \mathcal AV(y)\le -c_1V(y)+\breve c_1\qquad\text{for all } y\in\mathbb R^d. \tag{A.7}
--   $$
--
--   This Lyapunov function drives every ergodicity and moment estimate of the paper, for the diffusion (Lemma A.1) and for the Euler–Maruyama chain (Lemma A.4, Proposition 2.1).
--
--   **Formalization Note** The paper takes $\tilde Q$ from Dieker and Gao [19, Theorem 1], and the constants $\kappa$ and $c_1,\check c_1,\hat c_1,\hat c_2,\hat C_1,\hat C_2$ from their proof of Theorem 3; the statement asserts their existence. The inequality $A<0$ is negative definiteness, $A\le0$ negative semidefiniteness.
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, pp. 23-24, (A.4)-(A.7)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_GPhNGIDiffusion_EMError_Model
import Definitions.Def_GPhNGIDiffusion_EMError_Diffusion
import Definitions.Def_GPhNGIDiffusion_EMError_Lyapunov

open Matrix

namespace GPhNGIDiffusion.EMError

/-- (A.4)–(A.7), pp. 23–24: for every model there are a positive definite matrix `Q̃` with
`∑ |Q̃_ij| = 1`, `Q̃(−R) + (−R)′Q̃ < 0` and `Q̃(−(I − pe′)R) + (−R′(I − ep′))Q̃ ≤ 0`, and constants
`κ, ĉ₂ > 0`, such that `V(y) = (e′y)² + κ[y − pφ(e′y)]′Q̃[y − pφ(e′y)] + ĉ₂` is a `C²` Lyapunov
function satisfying (A.5), (A.6) and (A.7) with some constants `c₁, c̆₁ > 0`. -/
theorem lyapunov_A4_A7 {d : ℕ} (M : Model d) :
    ∃ (Q : Matrix (Fin d) (Fin d) ℝ) (κ c2 c₁ c₁' : ℝ),
      Q.PosDef ∧ (∑ i, ∑ j, |Q i j|) = 1 ∧
      (-(Q * M.R + M.Rᵀ * Q)).PosDef ∧
      (Q * ((1 - Matrix.of (fun i (_ : Fin d) => M.p i)) * M.R)
        + (M.Rᵀ * (1 - Matrix.of (fun (_ : Fin d) j => M.p j))) * Q).PosSemidef ∧
      0 < κ ∧ 0 < c2 ∧
      IsLyapunovFn M (lyapunovA4 M Q κ c2) c₁ c₁' := by sorry

end GPhNGIDiffusion.EMError
