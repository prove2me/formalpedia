-- Prove2me | Theorems.Thm_GeneralizedComplex_eigenbundle_correspondence
-- name    : GeneralizedComplex.eigenbundle_correspondence
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T23:45:10.319979+00:00
-- url     : https://prove2.me/theorems/29e5fe35-8183-428f-9794-cd866ad5d419
-- title:
--   Generalized almost complex structures $\leftrightarrow$ maximal isotropic $L$ with $L\cap\bar L=0$
-- statement:
--   Let $T=\mathbb R^N$ and equip $T\oplus T^*$ with $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$.
--
--   1. If $\mathcal J$ is a generalized almost complex structure (a real linear map with $\mathcal J^2=-\mathrm{Id}$ preserving $\langle\cdot,\cdot\rangle$), its $\sqrt{-1}$-eigenbundle $L\subseteq(T\oplus T^*)\otimes\mathbb C$ is maximal isotropic and satisfies $L\cap\bar L=0$.
--   2. Conversely, for every complex subspace $L$ which is maximal isotropic and satisfies $L\cap\bar L=0$, there is a **unique** generalized almost complex structure $\mathcal J$ with
--   $$L=\{v\in(T\oplus T^*)\otimes\mathbb C:\ \mathcal Jv=\sqrt{-1}\,v\}.$$
--
--   Thus properties (i) $L\cap\bar L=0$ and (ii) maximal isotropy can be taken as an alternative definition of a generalized almost complex structure.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Definition > The generalized tangent bundle, eigenbundle paragraph and properties (i), (ii)

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem eigenbundle_correspondence (N : ℕ) :
    (∀ J : Matrix (GIdx N) (GIdx N) ℝ, IsGenAlmostComplex J →
      IsMaximalIsotropic (plusIEigenspace J) ∧
        plusIEigenspace J ⊓ conjSubmodule (plusIEigenspace J) = ⊥) ∧
    (∀ L : Submodule ℂ (GIdx N → ℂ), IsMaximalIsotropic L → L ⊓ conjSubmodule L = ⊥ →
      ∃! J : Matrix (GIdx N) (GIdx N) ℝ, IsGenAlmostComplex J ∧ plusIEigenspace J = L) := by sorry

end GeneralizedComplex
