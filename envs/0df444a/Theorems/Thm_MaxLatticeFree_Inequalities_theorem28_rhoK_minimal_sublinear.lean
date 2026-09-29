-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_theorem28_rhoK_minimal_sublinear
-- name    : MaxLatticeFree.Inequalities.theorem28_rhoK_minimal_sublinear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:15:26.651522+00:00
-- url     : https://prove2.me/theorems/a742be8b-33dc-4bc1-8167-e904cabfd5a8
-- title:
--   Theorem 28: $\rho_K$ represents $K$ and is the smallest such sublinear function
-- statement:
--   Let $W\subseteq\mathbb R^q$ be a linear subspace and $K\subseteq W$ a closed convex set containing the origin in its interior relative to $W$. Let $\rho_K(r)=\sup_{y\in\hat K}ry$ with $\hat K=\{y\in K^*\mid\exists x\in K,\ xy=1\}$ and $K^*=\{y\in W\mid ry\le1\ \forall r\in K\}$. Then
--   $$K=\{r\in W\mid \rho_K(r)\le1\},$$
--   and for every sublinear function $\sigma:W\to\mathbb R$ such that $K=\{r\in W\mid\sigma(r)\le1\}$ we have $\rho_K(r)\le\sigma(r)$ for every $r\in W$.
--
--   This result of Basu, Cornuéjols and Zambelli (cited as [9]) is the ingredient that produces, from any sublinear valid inequality, a pointwise smaller one determined by the convex set alone.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 18, Theorem 28 (Basu et al. [9])

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

namespace MaxLatticeFree.Inequalities

theorem theorem28_rhoK_minimal_sublinear {q : ℕ} (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (K : Set (EuclideanSpace ℝ (Fin q))) (hKW : K ⊆ W) (hclosed : IsClosed K) (hconv : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin q)) ∈ intRel (W : Set (EuclideanSpace ℝ (Fin q))) K) :
    (∀ r : W, (r : EuclideanSpace ℝ (Fin q)) ∈ K ↔ rhoK W K r ≤ 1) ∧
    ∀ σ : W → ℝ, IsSublinear σ → (∀ r : W, (r : EuclideanSpace ℝ (Fin q)) ∈ K ↔ σ r ≤ 1) →
      ∀ r : W, rhoK W K r ≤ σ r := by sorry

end MaxLatticeFree.Inequalities
