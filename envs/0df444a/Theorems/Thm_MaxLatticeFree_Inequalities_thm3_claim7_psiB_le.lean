-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_thm3_claim7_psiB_le
-- name    : MaxLatticeFree.Inequalities.thm3_claim7_psiB_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:22:18.544162+00:00
-- url     : https://prove2.me/theorems/2fe33b69-645c-4bb5-8177-4cd64c3e0644
-- title:
--   Claim 7 in the proof of Theorem 3: $\psi''\ge\psi_B$ for a maximal lattice-free $B\supseteq B_{\psi''}$
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point. Let $\psi'':W\to\mathbb R$ be sublinear and nonnegative, with $\sum_{r\in W}\psi''(r)s_r\ge1$ valid for $R_f(W)$, and let $B$ be a maximal lattice-free convex set in $f+W$ containing $B_{\psi''}=\{x\in f+W\mid\psi''(x-f)\le1\}$. Then
--   $$\psi''(r)\ \ge\ \psi_B(r)\qquad\text{for all } r\in W .$$
--
--   **Formalization Note** The context of the claim on p. 21 is in the hypotheses. $\psi_B=\rho_{B-f}$ (see the Polar definition).
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 21, Claim 7 in the proof of Theorem 3

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

namespace MaxLatticeFree.Inequalities

theorem thm3_claim7_psiB_le {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ'' : W → ℝ)
    (hsub : IsSublinear ψ'') (hnonneg : ∀ r, 0 ≤ ψ'' r) (hvalid : IsValid f W ψ'' 1)
    (B : Set (EuclideanSpace ℝ (Fin q))) (hB : IsMaximalLatticeFree f W B) (hBB : Bpsi f W ψ'' 1 ⊆ B) :
    ∀ r : W, psiB f W B r ≤ ψ'' r := by sorry

end MaxLatticeFree.Inequalities
