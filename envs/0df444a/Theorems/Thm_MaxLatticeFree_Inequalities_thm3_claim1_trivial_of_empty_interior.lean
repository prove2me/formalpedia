-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_thm3_claim1_trivial_of_empty_interior
-- name    : MaxLatticeFree.Inequalities.thm3_claim1_trivial_of_empty_interior
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:12:11.664165+00:00
-- url     : https://prove2.me/theorems/b9646048-79ef-4d92-9f3f-a38a94aee4e4
-- title:
--   Claim 1 in the proof of Theorem 3: if $\operatorname{int}(B_\psi)\cap V=\emptyset$ the inequality is trivial
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point, and let $V$ be the affine hull of $(f+W)\cap\mathbb Z^q$. Let $\sum_{r\in W}\psi(r)s_r\ge\alpha$ be a valid inequality for $R_f(W)$ with $\psi$ sublinear. If no point $x\in V$ satisfies $\psi(x-f)<\alpha$, that is,
--   $$\{x\in f+W\mid\psi(x-f)<\alpha\}\cap V=\emptyset,$$
--   then the inequality is trivial: it holds for every $s\in\mathcal V$ with $s\ge0$.
--
--   **Formalization Note** $\operatorname{int}(B_\psi)$ is read as the paper defines it on p. 17, $\{x\in f+W\mid\psi(x-f)<\alpha\}$. The context of the claim (a nontrivial valid inequality, made sublinear by Lemma 23) enters as the hypotheses "valid" and "sublinear"; nontriviality is omitted because the claim concludes triviality (with it the statement would be logically equivalent).
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 19, Claim 1 in the proof of Theorem 3

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

namespace MaxLatticeFree.Inequalities

theorem thm3_claim1_trivial_of_empty_interior {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ : W → ℝ) (α : ℝ)
    (hvalid : IsValid f W ψ α) (hsub : IsSublinear ψ)
    (hempty : Disjoint (intBpsi f W ψ α) (affHullInt f W : Set (EuclideanSpace ℝ (Fin q)))) :
    IsTrivial f W ψ α := by sorry

end MaxLatticeFree.Inequalities
