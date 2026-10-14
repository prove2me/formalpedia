-- Prove2me | Theorems.Thm_GeneralizedComplex_eq_of_plusIEigenspace_eq
-- name    : GeneralizedComplex.eq_of_plusIEigenspace_eq
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:47:59.360272+00:00
-- url     : https://prove2.me/theorems/36ba385d-67d9-4737-8a06-4cd272961bd3
-- title:
--   A generalized almost complex structure is determined by its $\sqrt{-1}$-eigenbundle
-- statement:
--   Let $\mathcal J_1,\mathcal J_2$ be generalized almost complex structures on $T\oplus T^*$ with the same $\sqrt{-1}$-eigenbundle:
--   $$\{v:\mathcal J_1v=\sqrt{-1}\,v\}=\{v:\mathcal J_2v=\sqrt{-1}\,v\}.$$
--   Then $\mathcal J_1=\mathcal J_2$.
--
--   This is the uniqueness half of the eigenbundle correspondence.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Definition > The generalized tangent bundle, first sentence of the eigenbundle paragraph

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem eq_of_plusIEigenspace_eq {N : ℕ} (J₁ J₂ : Matrix (GIdx N) (GIdx N) ℝ)
    (h₁ : IsGenAlmostComplex J₁) (h₂ : IsGenAlmostComplex J₂)
    (h : plusIEigenspace J₁ = plusIEigenspace J₂) : J₁ = J₂ := by sorry

end GeneralizedComplex
