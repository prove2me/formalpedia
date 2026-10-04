-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_remark29_rhoK_polyhedral
-- name    : MaxLatticeFree.Inequalities.remark29_rhoK_polyhedral
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:19:09.589985+00:00
-- url     : https://prove2.me/theorems/113f0655-d0c5-4345-93f0-aaa1d53254c6
-- title:
--   Remark 29 (tight rows): $\rho_K(r)=\max_i a_ir$ for a polyhedron $K=\{r\in W\mid a_ir\le1\}$
-- statement:
--   Let $W\subseteq\mathbb R^q$ be a linear subspace, $t\ge1$, and $a_1,\dots,a_t\in W$. Let $K=\{r\in W\mid a_ir\le1,\ i=1,\dots,t\}$, a polyhedron containing the origin in its interior relative to $W$, and suppose every row is tight: for each $i$ there is $r\in K$ with $a_ir=1$. Then for every $r\in W$
--   $$\rho_K(r)=\max_{i=1,\dots,t}a_ir .$$
--
--   This identifies the representation-free $\rho_K$ with the familiar piecewise-linear function of a polyhedron, and hence $\psi_B$ with eq. (4).
--
--   **Formalization Note** The paper states the remark without the tightness hypothesis, and it is false then: for $W=\mathbb R$ and $K=(-\infty,1]$ written with $a_1=1$, $a_2=1/2$, one has $K^*=[0,1]$, $\hat K=\{1\}$, $\rho_K(r)=r$, but $\max(r,r/2)=r/2$ for $r<0$. The paper applies it only to tight rows (Claim 5 arranges $\sup_{x\in B_\psi}a_i(x-f)=1$), so the tight version is stated. For a polyhedron, "$\sup_{r\in K}a_ir=1$" and "$a_ir=1$ for some $r\in K$" coincide. $t\ge1$ makes the maximum well defined.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 18, Remark 29

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

open scoped RealInnerProductSpace

namespace MaxLatticeFree.Inequalities

theorem remark29_rhoK_polyhedral {q t : ℕ} [NeZero t] (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (K : Set (EuclideanSpace ℝ (Fin q))) (a : Fin t → EuclideanSpace ℝ (Fin q)) (ha : ∀ i, a i ∈ W)
    (hK : K = {r | r ∈ W ∧ ∀ i, ⟪a i, r⟫ ≤ 1})
    (h0 : (0 : EuclideanSpace ℝ (Fin q)) ∈ intRel (W : Set (EuclideanSpace ℝ (Fin q))) K)
    (htight : ∀ i, ∃ r ∈ K, ⟪a i, r⟫ = 1) :
    ∀ r : W, rhoK W K r = Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫) := by sorry

end MaxLatticeFree.Inequalities
