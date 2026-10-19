-- Prove2me | Theorems.Thm_GeneralizedComplex_bShift_pairing
-- name    : GeneralizedComplex.bShift_pairing
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T23:53:23.006188+00:00
-- url     : https://prove2.me/theorems/a05ce8f3-93ce-4df1-988b-1aec0f3f2054
-- title:
--   B-field shifts are isometries
-- statement:
--   Let $B$ be a real 2-form on $T=\mathbb R^N$ (a skew-symmetric matrix, $B^{\mathsf T}=-B$) and let $e^B(X+\xi)=X+\xi+i_XB$. Then for all $u,v\in T\oplus T^*$,
--   $$\langle e^Bu,e^Bv\rangle=\langle u,v\rangle.$$
--
--   So B-field shifts preserve the natural inner product of the generalized tangent space.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Maximal isotropic subbundles > Type, paragraph 2

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem bShift_pairing {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = -B)
    (u v : GIdx N → ℝ) :
    pairing (bShift B *ᵥ u) (bShift B *ᵥ v) = pairing u v := by sorry

end GeneralizedComplex
