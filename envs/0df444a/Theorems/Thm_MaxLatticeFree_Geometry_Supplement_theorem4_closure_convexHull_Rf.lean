-- Prove2me | Theorems.Thm_MaxLatticeFree_Geometry_Supplement_theorem4_closure_convexHull_Rf
-- name    : MaxLatticeFree.Geometry.Supplement.theorem4_closure_convexHull_Rf
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T19:02:54.720797+00:00
-- url     : https://prove2.me/theorems/2b813ef3-a72e-4790-9842-553c3420bcd1
-- title:
--   Theorem 4 (corrected: ℬ_W read in f + W) — the ‖·‖_H-closure of conv R_f(W) is cut out by the inequalities of maximal lattice-free sets
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point; $W$ may be irrational and $f$ need not lie in $W$. Let $V=\operatorname{aff}((f+W)\cap\mathbb Z^q)$, let $\mathcal W$ be the finitely supported functions $s:W\to\mathbb R$, let
--
--   $$
--   R_f(W)=\Big\{s\in\mathcal W \ \Big|\ f+\sum_{r\in W}rs_r\in\mathbb Z^q,\ s\ge0\Big\},\qquad \mathcal V=\Big\{s\in\mathcal W\ \Big|\ f+\sum_{r\in W}rs_r\in V\Big\},
--   $$
--
--   and let $\mathcal B_W$ be the family of maximal lattice-free convex sets $B$ of $f+W$ with $f$ in their interior relative to $f+W$. For $B\in\mathcal B_W$, $\psi_B(r)=\max_i a_ir$ for any description $B=\{x\in f+W\mid a_i(x-f)\le1\}$ with tight rows. Then the closure in the norm $\|\cdot\|_H$ of the convex hull of $R_f(W)$ is
--
--   $$
--   \overline{\operatorname{conv}}(R_f(W))=\Big\{s\in\mathcal V\ \Big|\ \sum_{r\in W}\psi_B(r)s_r\ge1\ \ \forall B\in\mathcal B_W;\ \ s_r\ge0\ \ \forall r\in W\Big\}.
--   $$
--
--   Both inclusions are asserted. In finite dimension the closed convex hull is the intersection of the half-spaces containing it; in the infinite-dimensional space $\mathcal W$ this depends on the norm (for the Euclidean norm on $\mathcal W$ the identity fails, p. 6), and the theorem says that $\|\cdot\|_H$ is a norm in which the cuts of maximal lattice-free sets describe the closed convex hull.
--
--   **Formalization Note** $\mathcal W$ is `W →₀ ℝ`, conv is `convexHull ℝ`, the closure is `closureH`, and $\psi_B$ is the published `psiB f W B` $=\rho_{B-f}$, which equals $\max_ia_ir$ for every tight description. $B$ ranges over all of $\mathcal B_W$, including sets whose $\psi_B$ takes negative values; $\mathcal B_W$ is empty when $f$ is integral, and that case stays in the statement.
--
--   Differences from the source:
--   - correction: ℬ_W is the family of maximal lattice-free convex sets of W with f in their interior → maximal lattice-free convex sets of f + W with f in their interior relative to f + W; reason: read literally the family is empty whenever f ∉ W and the theorem is false: for q = 2, W = ℝ×{0}, f = (1/2, 1), s = 0 lies in the right-hand side but ∑|r₁|s_r ≥ 1/2 on conv R_f(W) and is ‖·‖_H-continuous, so 0 is not in the closure; the construction of ψ_B on p. 4 and Theorem 3 (p. 6) use sets of f + W; the proof on p. 23 invokes Theorem 3, supporting this translated family although its final sentence repeats W
--   - reading: ψ_B(r) = max_i a_i r for a row description of B (4) → the published psiB = ρ_{B−f}; reason: (4) depends on the description when it has non-tight rows; ρ_{B−f} is description-free and equals (4) for every tight description (Remark 29), which is the description the paper uses
--   - encoding: the closure Ā in ‖·‖_H, conv, 𝒲 → closureH (ε-closure in normH), convexHull ℝ, W →₀ ℝ; reason: same sets
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 7, Theorem 4 (with ‖·‖_H and ℬ_W defined on p. 7)

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_LatticeFree
import Definitions.Def_MaxLatticeFree_Inequalities_Polar
import Definitions.Def_MaxLatticeFree_Geometry_Supplement_NormH

open MaxLatticeFree.Inequalities

namespace MaxLatticeFree.Geometry.Supplement

theorem theorem4_closure_convexHull_Rf {q : ℕ} (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hint : (affSpace f W ∩ integralPoints q).Nonempty) :
    closureH (convexHull ℝ (Rf f W)) =
      {s | s ∈ calV f W ∧ (∀ r, 0 ≤ s r) ∧
        ∀ B : Set (EuclideanSpace ℝ (Fin q)), IsMaximalLatticeFree f W B →
          f ∈ intRel (affSpace f W) B → 1 ≤ linVal (psiB f W B) s} := by sorry

end MaxLatticeFree.Geometry.Supplement
