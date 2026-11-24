-- Prove2me | Theorems.Thm_IdentifiableVAE_sim_equivalence
-- name    : IdentifiableVAE.sim_equivalence
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T06:57:42.746813+00:00
-- url     : https://prove2.me/theorems/1893e23c-82e8-4ce3-b631-254ff0afdf60
-- title:
--   Proposition 2: $\sim_A$ and $\sim_P$ are equivalence relations
-- statement:
--   Fix a set $X\subset\mathbb{R}^d$ and consider the parameters $\theta=(f,Q,T,\lambda)$ whose mixing function $f:\mathbb{R}^n\to\mathbb{R}^d$ is injective with image $f(\mathbb{R}^n)=X$. On this set of parameters, the relation $\sim_A$ of Definition 2 is an equivalence relation, where
--
--   $$\theta\sim_A\tilde\theta\iff\exists A\in GL_{nk}(\mathbb{R}),\ c\in\mathbb{R}^{nk}:\ \mathbf T(f^{-1}(x))=A\,\tilde{\mathbf T}(\tilde f^{-1}(x))+c\quad\forall x\in X.$$
--
--   The relation $\sim_P$, which requires in addition that $A$ is a block permutation matrix, is also an equivalence relation.
--
--   This makes the identifiability classes of Definition 1 well defined.
--
--   **Formalization Note** The paper states the result on all of $\Theta$ with $X$ the common image of the mixing functions. The statement restricts to parameters with a common image $X$, because symmetry fails when two mixing functions have different images.
-- source:
--   Khemakhem, Kingma, Monti and Hyvärinen, Variational Autoencoders and Nonlinear ICA: A Unifying Framework, AISTATS 2020, arXiv:1907.04809v4, Appendix B.1, Proposition 2 (proof of Definition 2, eq. (13)), p. 12

import Mathlib
import Definitions.Def_IdentifiableVAE_Basic

open MeasureTheory

namespace IdentifiableVAE

theorem sim_equivalence {n d m k : ℕ} (X : Set (EuclideanSpace ℝ (Fin d))) :
    Equivalence (fun θ θ' : {θ : Param n d m k // Function.Injective θ.f ∧ Set.range θ.f = X} =>
      SimA θ.1 θ'.1) ∧
    Equivalence (fun θ θ' : {θ : Param n d m k // Function.Injective θ.f ∧ Set.range θ.f = X} =>
      SimP θ.1 θ'.1) := by sorry

end IdentifiableVAE
