-- Prove2me | Theorems.Thm_GeneralizedComplex_exists_eq_isotropicOfPair
-- name    : GeneralizedComplex.exists_eq_isotropicOfPair
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:51:10.929217+00:00
-- url     : https://prove2.me/theorems/dceb314e-991e-41d6-b221-cef68cbedd27
-- title:
--   Every maximal isotropic subspace is of the form $L(E,\varepsilon)$
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$ and let $L\subseteq\mathbb K^N\oplus(\mathbb K^N)^*$ be a maximal isotropic subspace. Then there are a subspace $E\subseteq\mathbb K^N$ and a 2-form $\varepsilon$ on $E$ (a skew bilinear form) such that
--   $$L=L(E,\varepsilon)=\{X+\xi:\ X\in E,\ \xi|_E=\varepsilon(X,\cdot)\}.$$
--
--   This is Gualtieri's classification of maximal isotropic subspaces.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Maximal isotropic subbundles > Classification, last sentence of paragraph 3 (Gualtieri)

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem exists_eq_isotropicOfPair {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (L : Submodule 𝕜 (GIdx N → 𝕜)) (hL : IsMaximalIsotropic L) :
    ∃ (E : Submodule 𝕜 (Fin N → 𝕜)) (ε : LinearMap.BilinForm 𝕜 E),
      (∀ X Y : E, ε X Y = -ε Y X) ∧ L = isotropicOfPair E ε := by sorry

end GeneralizedComplex
