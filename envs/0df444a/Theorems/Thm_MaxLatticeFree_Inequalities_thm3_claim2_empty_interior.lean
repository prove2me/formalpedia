-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_thm3_claim2_empty_interior
-- name    : MaxLatticeFree.Inequalities.thm3_claim2_empty_interior
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:14:15.380603+00:00
-- url     : https://prove2.me/theorems/608d75c1-f9c2-4f98-9b4e-e07e8539e459
-- title:
--   Claim 2 in the proof of Theorem 3: if $f\in V$ and $\alpha\le0$ then $\operatorname{int}(B_\psi)\cap V=\emptyset$
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point, and let $V$ be the affine hull of $(f+W)\cap\mathbb Z^q$. Let $\sum_{r\in W}\psi(r)s_r\ge\alpha$ be a valid inequality for $R_f(W)$ with $\psi$ sublinear. If $f\in V$ and $\alpha\le0$, then
--   $$\{x\in f+W\mid\psi(x-f)<\alpha\}\cap V=\emptyset .$$
--
--   Together with Claim 1 this shows that a nontrivial valid inequality with $f\in V$ has $\alpha>0$, so it can be rescaled to right-hand side $1$.
--
--   **Formalization Note** $\operatorname{int}(B_\psi)$ is read as the paper defines it on p. 17, $\{x\in f+W\mid\psi(x-f)<\alpha\}$. With the topological relative interior the claim is false at $\alpha=0$: for $\psi\equiv0$, $\alpha=0$ and $f$ integral the inequality $0\ge0$ is valid, $f\in V$, and the relative interior of $B_\psi=f+W$ meets $V$.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 19, Claim 2 in the proof of Theorem 3

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

namespace MaxLatticeFree.Inequalities

theorem thm3_claim2_empty_interior {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ : W → ℝ) (α : ℝ)
    (hvalid : IsValid f W ψ α) (hsub : IsSublinear ψ)
    (hfV : f ∈ affHullInt f W) (hα : α ≤ 0) :
    Disjoint (intBpsi f W ψ α) (affHullInt f W : Set (EuclideanSpace ℝ (Fin q))) := by sorry

end MaxLatticeFree.Inequalities
