-- Prove2me | Theorems.Thm_GeneralizedComplex_symplecticGen_spec
-- name    : GeneralizedComplex.symplecticGen_spec
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T23:55:19.345364+00:00
-- url     : https://prove2.me/theorems/578d3950-b5f6-4174-b6e2-ca19f2d0a997
-- title:
--   Symplectic forms are generalized complex of type $0$
-- statement:
--   Let $\omega$ be a nondegenerate real 2-form on $T=\mathbb R^N$ (a skew matrix with $\det\omega\ne0$), and write $\omega^\flat X=i_X\omega$. Then
--   $$\mathcal J_\omega(X+\xi)=-(\omega^\flat)^{-1}\xi+\omega^\flat X$$
--   is a generalized almost complex structure on $T\oplus T^*$, and its type equals $0$.
--
--   This is the pointwise content of the statement that symplectic manifolds are generalized complex manifolds of type $0$.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Examples > Symplectic manifolds

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem symplecticGen_spec {N : ℕ} (ω : Matrix (Fin N) (Fin N) ℝ) (hω : ωᵀ = -ω)
    (hdet : ω.det ≠ 0) :
    IsGenAlmostComplex (symplecticGen ω) ∧ genType (plusIEigenspace (symplecticGen ω)) = 0 := by
  sorry

end GeneralizedComplex
