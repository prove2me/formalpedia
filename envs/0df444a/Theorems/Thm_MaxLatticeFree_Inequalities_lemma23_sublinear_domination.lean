-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_lemma23_sublinear_domination
-- name    : MaxLatticeFree.Inequalities.lemma23_sublinear_domination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:00:43.04198+00:00
-- url     : https://prove2.me/theorems/33c3d26d-d046-4c10-af2f-650aa6313eaa
-- title:
--   Lemma 23: every valid inequality is dominated by a valid sublinear one
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point. Let $\psi:W\to\mathbb R$ be any function and $\alpha\in\mathbb R$ such that
--   $$\sum_{r\in W}\psi(r)s_r\ \ge\ \alpha$$
--   is valid for $R_f(W)$. Then there is a **sublinear** function $\psi':W\to\mathbb R$ with $\psi'(r)\le\psi(r)$ for all $r\in W$ such that $\sum_{r\in W}\psi'(r)s_r\ge\alpha$ is also valid for $R_f(W)$.
--
--   This reduces the study of valid inequalities to those with sublinear (hence convex and continuous) coefficient functions, which is what makes the geometric set $B_\psi$ available.
--
--   **Formalization Note** The standing assumption of p. 4 that $f+W$ contains an integral point is a hypothesis; without it $R_f(W)$ is empty, every inequality is valid and the lemma fails.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 15, Lemma 23

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

namespace MaxLatticeFree.Inequalities

theorem lemma23_sublinear_domination {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ : W → ℝ) (α : ℝ)
    (hvalid : IsValid f W ψ α) :
    ∃ ψ' : W → ℝ, IsValid f W ψ' α ∧ Dominates ψ' ψ ∧ IsSublinear ψ' := by sorry

end MaxLatticeFree.Inequalities
