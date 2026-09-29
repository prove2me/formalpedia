-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_remark30_rhoK_valid
-- name    : MaxLatticeFree.Inequalities.remark30_rhoK_valid
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:16:27.368699+00:00
-- url     : https://prove2.me/theorems/fabda8f7-c7f8-43eb-be46-963e702546ca
-- title:
--   Remark 30: a closed lattice-free convex set with $f$ in its interior gives the valid inequality $\sum\rho_K(r)s_r\ge1$
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point. Let $B$ be a closed lattice-free convex set in $f+W$ with $f$ in its interior relative to $f+W$, and let $K=B-f$. Then the inequality
--   $$\sum_{r\in W}\rho_K(r)s_r\ \ge\ 1$$
--   is valid for $R_f(W)$.
--
--   This is the basic mechanism by which lattice-free sets produce cuts.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 18, Remark 30

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

namespace MaxLatticeFree.Inequalities

theorem remark30_rhoK_valid {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (B : Set (EuclideanSpace ℝ (Fin q)))
    (hclosed : IsClosed B) (hB : IsLatticeFree f W B) (hfB : f ∈ intRel (affSpace f W) B) :
    IsValid f W (rhoK W ((fun x => x - f) '' B)) 1 := by sorry

end MaxLatticeFree.Inequalities
