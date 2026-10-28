-- Prove2me | Theorems.Thm_GeneralizedComplex_complexStructureGen_spec
-- name    : GeneralizedComplex.complexStructureGen_spec
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T23:54:49.478638+00:00
-- url     : https://prove2.me/theorems/ded06f95-34bb-46e8-bdf8-158c8e72100a
-- title:
--   Complex structures are generalized complex of type $N$
-- statement:
--   Let $J_0$ be a linear complex structure on $T=\mathbb R^N$, i.e. $J_0^2=-1$. Then
--   $$\mathcal J_{J_0}(X+\xi)=-J_0X+\xi\circ J_0$$
--   is a generalized almost complex structure on $T\oplus T^*$, and its type equals $N$.
--
--   This is the pointwise content of the statement that complex manifolds are generalized complex manifolds of type $N$.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Examples > Complex manifolds

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem complexStructureGen_spec {N : ℕ} (J₀ : Matrix (Fin N) (Fin N) ℝ) (hJ₀ : J₀ * J₀ = -1) :
    IsGenAlmostComplex (complexStructureGen J₀) ∧
      genType (plusIEigenspace (complexStructureGen J₀)) = N := by sorry

end GeneralizedComplex
