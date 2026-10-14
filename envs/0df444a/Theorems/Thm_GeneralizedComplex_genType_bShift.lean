-- Prove2me | Theorems.Thm_GeneralizedComplex_genType_bShift
-- name    : GeneralizedComplex.genType_bShift
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:54:01.414777+00:00
-- url     : https://prove2.me/theorems/8fa00702-5d09-45e0-acb3-234487cf6302
-- title:
--   The type is invariant under B-field shifts
-- statement:
--   Let $\mathcal J$ be a generalized almost complex structure on $T\oplus T^*$ and $B$ a real 2-form on $T$. Then the B-field transform $e^B\mathcal J e^{-B}$ is again a generalized almost complex structure, and
--   $$\operatorname{type}\bigl(L_{e^B\mathcal Je^{-B}}\bigr)=\operatorname{type}(L_{\mathcal J}),$$
--   where $L_{\mathcal J}$ denotes the $\sqrt{-1}$-eigenbundle.
--
--   **Formalization Note** At the level of a single fiber the closedness of $B$ required in the source plays no role (it matters only for integrability), so $B$ is an arbitrary skew matrix.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Maximal isotropic subbundles > Type, paragraph 2

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem genType_bShift {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ) (hJ : IsGenAlmostComplex J)
    (B : Matrix (Fin N) (Fin N) ℝ) (hB : Bᵀ = -B) :
    IsGenAlmostComplex (bShift B * J * bShift (-B)) ∧
      genType (plusIEigenspace (bShift B * J * bShift (-B))) = genType (plusIEigenspace J) := by
  sorry

end GeneralizedComplex
