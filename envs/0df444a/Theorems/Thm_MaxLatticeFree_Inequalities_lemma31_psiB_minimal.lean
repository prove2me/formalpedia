-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_lemma31_psiB_minimal
-- name    : MaxLatticeFree.Inequalities.lemma31_psiB_minimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:23:04.980924+00:00
-- url     : https://prove2.me/theorems/716fc8b2-8d5d-4840-9e36-593fc01634bb
-- title:
--   Lemma 31: $\sum\psi_B(r)s_r\ge1$ is minimal for a maximal lattice-free $B$ with $f$ in its interior
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point. Let $B$ be a maximal lattice-free convex set in $f+W$ containing $f$ in its interior relative to $f+W$. Then
--   $$\sum_{r\in W}\psi_B(r)s_r\ \ge\ 1$$
--   is a minimal valid inequality for $R_f(W)$.
--
--   This is the easy half of the correspondence of Theorem 3: maximal lattice-free sets give minimal inequalities.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 19, Lemma 31

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

namespace MaxLatticeFree.Inequalities

theorem lemma31_psiB_minimal {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (B : Set (EuclideanSpace ℝ (Fin q)))
    (hB : IsMaximalLatticeFree f W B) (hfB : f ∈ intRel (affSpace f W) B) :
    IsMinimal f W (psiB f W B) 1 := by sorry

end MaxLatticeFree.Inequalities
