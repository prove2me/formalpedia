-- Prove2me | Theorems.Thm_MaxLatticeFree_Inequalities_thm3_claim6_nonnegative_equivalent
-- name    : MaxLatticeFree.Inequalities.thm3_claim6_nonnegative_equivalent
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:21:34.568418+00:00
-- url     : https://prove2.me/theorems/7a46607e-7e87-4df8-88dc-9f9bd6ccc020
-- title:
--   Claim 6 in the proof of Theorem 3: some $\lambda$ makes $\psi(r)+\lambda^TCr$ nonnegative on $W$
-- statement:
--   Let $f\in\mathbb R^q$ and $W\subseteq\mathbb R^q$ a linear subspace such that $f+W$ contains an integral point, and let $C\in\mathbb R^{\ell\times q}$, $d\in\mathbb R^\ell$ with $V=\{x\in f+W\mid Cx=d\}$. Let $t\ge1$, $a_1,\dots,a_t\in\mathbb R^q$ (the rows of $A\in\mathbb R^{t\times q}$) and let $\psi:W\to\mathbb R$ be given by
--   $$\psi(r)=\max_{i=1,\dots,t}a_ir\qquad(r\in W),$$
--   with $\sum_{r\in W}\psi(r)s_r\ge1$ valid for $R_f(W)$. Assume that the recession cone of $B_\psi\cap V$ equals its lineality space, in the form
--   $$\{r\in W\mid Ar\le0,\ Cr=0\}=\{r\in W\mid Ar=0,\ Cr=0\}.$$
--   Then there exists $\lambda\in\mathbb R^\ell$ such that $\psi(r)+\lambda^TCr\ge0$ for all $r\in W$.
--
--   This is the step that turns a minimal inequality into an equivalent one with nonnegative coefficients.
--
--   **Formalization Note** The context of the claim on pp. 20–21 is in the hypotheses: eq. (11) for $\psi$, validity, and $\operatorname{rec}(B_\psi\cap V)=\operatorname{lin}(B_\psi\cap V)$, written as the paper computes the two cones on p. 21 (with $W=\{r\mid Gr=0\}$). The algebraic form avoids the convention for the recession cone of an empty set.
-- source:
--   Basu, Conforti, Cornuéjols, Zambelli, Maximal lattice-free convex sets in linear subspaces, arXiv:1701.06543v1, p. 20, Claim 6 in the proof of Theorem 3 (context: eq. (11) p. 20, cones on p. 21)

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

open Matrix
open scoped RealInnerProductSpace

namespace MaxLatticeFree.Inequalities

theorem thm3_claim6_nonnegative_equivalent {q ℓ t : ℕ} [NeZero t] (f : EuclideanSpace ℝ (Fin q))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (hf : (affSpace f W ∩ integralPoints q).Nonempty)
    (C : Matrix (Fin ℓ) (Fin q) ℝ) (d : Fin ℓ → ℝ) (hCd : IsAffineHullDescription f W C d)
    (a : Fin t → EuclideanSpace ℝ (Fin q)) (ψ : W → ℝ)
    (hψ : ∀ r : W, ψ r = Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫))
    (hvalid : IsValid f W ψ 1)
    (hrec : {r : EuclideanSpace ℝ (Fin q) | r ∈ W ∧ (∀ i, ⟪a i, r⟫ ≤ 0) ∧ C *ᵥ r.ofLp = 0} =
      {r : EuclideanSpace ℝ (Fin q) | r ∈ W ∧ (∀ i, ⟪a i, r⟫ = 0) ∧ C *ᵥ r.ofLp = 0}) :
    ∃ lam : Fin ℓ → ℝ, ∀ r : W, 0 ≤ ψ r + lam ⬝ᵥ (C *ᵥ (r : EuclideanSpace ℝ (Fin q)).ofLp) := by sorry

end MaxLatticeFree.Inequalities
