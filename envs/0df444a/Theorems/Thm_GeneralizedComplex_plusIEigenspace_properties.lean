-- Prove2me | Theorems.Thm_GeneralizedComplex_plusIEigenspace_properties
-- name    : GeneralizedComplex.plusIEigenspace_properties
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:45:38.774515+00:00
-- url     : https://prove2.me/theorems/4c560cad-59d1-4cb1-9648-d6384fc3d157
-- title:
--   Properties (i), (ii) of the $\sqrt{-1}$-eigenbundle
-- statement:
--   Let $\mathcal J$ be a generalized almost complex structure on $T\oplus T^*$ and let $L\subseteq(T\oplus T^*)\otimes\mathbb C$ be its $\sqrt{-1}$-eigenbundle. Then
--
--   1. $L\cap\bar L=0$;
--   2. $L$ is maximal isotropic: $\dim_{\mathbb C}L=N$ and $\langle\ell,\ell'\rangle=0$ for all $\ell,\ell'\in L$.
--
--   These are the two properties that characterize eigenbundles of generalized almost complex structures.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Definition > The generalized tangent bundle, properties (i) and (ii)

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem plusIEigenspace_properties {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ)
    (hJ : IsGenAlmostComplex J) :
    plusIEigenspace J ⊓ conjSubmodule (plusIEigenspace J) = ⊥ ∧
      IsMaximalIsotropic (plusIEigenspace J) := by sorry

end GeneralizedComplex
