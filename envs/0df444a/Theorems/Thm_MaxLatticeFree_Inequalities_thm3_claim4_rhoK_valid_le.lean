-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_thm3_claim4_rhoK_valid_le
-- name    : MaxLatticeFree.Inequalities.thm3_claim4_rhoK_valid_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:17:05.963856+00:00
-- url     : https://prove2.me/theorems/faf29a99-40a4-4f42-baac-b2e18c6d5f58
-- title:
--   Claim 4 in the proof of Theorem 3: $\sum\rho_K(r)s_r\ge1$ is valid and $\psi\ge\rho_K$
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point. Let $\psi:W\to\mathbb R$ be sublinear with $\sum_{r\in W}\psi(r)s_r\ge1$ valid for $R_f(W)$, and let $K=\{r\in W\mid\psi(r)\le1\}$. Then the inequality
--   $$\sum_{r\in W}\rho_K(r)s_r\ \ge\ 1$$
--   is valid for $R_f(W)$, and $\psi(r)\ge\rho_K(r)$ for all $r\in W$.
--
--   **Formalization Note** The context of the claim on p. 19 (a valid inequality with right-hand side $1$ and sublinear $\psi$) is taken as the hypotheses.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 19, Claim 4 in the proof of Theorem 3

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

namespace MaxLatticeFree.Inequalities

theorem thm3_claim4_rhoK_valid_le {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ : W → ℝ)
    (hvalid : IsValid f W ψ 1) (hsub : IsSublinear ψ) :
    IsValid f W (rhoK W ((fun r : W => (r : EuclideanSpace ℝ (Fin q))) '' {r | ψ r ≤ 1})) 1 ∧
    ∀ r : W, rhoK W ((fun r : W => (r : EuclideanSpace ℝ (Fin q))) '' {r | ψ r ≤ 1}) r ≤ ψ r := by sorry

end MaxLatticeFree.Inequalities
