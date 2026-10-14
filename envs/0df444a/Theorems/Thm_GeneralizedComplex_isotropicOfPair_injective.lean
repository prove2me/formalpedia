-- Prove2me | Theorems.Thm_GeneralizedComplex_isotropicOfPair_injective
-- name    : GeneralizedComplex.isotropicOfPair_injective
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:51:40.39975+00:00
-- url     : https://prove2.me/theorems/b52bf71a-922f-4eba-9bb9-c14c6e81f254
-- title:
--   The pair $(E,\varepsilon)$ is determined by $L(E,\varepsilon)$
-- statement:
--   Let $\mathbb K$ be $\mathbb R$ or $\mathbb C$, let $E\subseteq\mathbb K^N$ be a subspace and let $\varepsilon,\varepsilon'$ be bilinear forms on $E$. Then
--
--   1. the projection of $L(E,\varepsilon)$ to $\mathbb K^N$ is exactly $E$;
--   2. if $L(E,\varepsilon)=L(E,\varepsilon')$ then $\varepsilon=\varepsilon'$.
--
--   Together these say that $(E,\varepsilon)\mapsto L(E,\varepsilon)$ is injective, which is the "one-to-one" part of the correspondence between maximal isotropic subspaces and pairs $(E,\varepsilon)$.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Maximal isotropic subbundles > Classification, paragraph 1 (one-to-one correspondence)

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem isotropicOfPair_injective {𝕜 : Type*} [RCLike 𝕜] {N : ℕ}
    (E : Submodule 𝕜 (Fin N → 𝕜)) (ε ε' : LinearMap.BilinForm 𝕜 E) :
    tangentProjection (isotropicOfPair E ε) = E ∧
      (isotropicOfPair E ε = isotropicOfPair E ε' → ε = ε') := by sorry

end GeneralizedComplex
