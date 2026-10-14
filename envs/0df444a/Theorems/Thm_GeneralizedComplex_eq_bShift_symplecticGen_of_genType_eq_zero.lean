-- Prove2me | Theorems.Thm_GeneralizedComplex_eq_bShift_symplecticGen_of_genType_eq_zero
-- name    : GeneralizedComplex.eq_bShift_symplecticGen_of_genType_eq_zero
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T23:55:50.44398+00:00
-- url     : https://prove2.me/theorems/c48b094c-6934-4515-9184-f91432dad32c
-- title:
--   Type-$0$ structures are B-shifts of symplectic ones
-- statement:
--   Let $\mathcal J$ be a generalized almost complex structure on $T\oplus T^*$ whose $\sqrt{-1}$-eigenbundle has type $0$. Then there are a real 2-form $B$ and a nondegenerate real 2-form $\omega$ on $T$ such that
--   $$\mathcal J=e^B\,\mathcal J_\omega\,e^{-B}.$$
--
--   This is the pointwise content of the statement that, up to a shift of the B-field, symplectic structures are the only type-$0$ generalized complex structures.
--
--   **Formalization Note** Pointwise, no closedness of $B$ or $\omega$ is involved; the global statement in the source additionally needs integrability.
--
--   Throughout, $T=\mathbb R^N$ models a tangent space of an $N$-manifold, $T^*$ its dual (identified with $\mathbb R^N$ via the standard dual basis), and $T\oplus T^*$ the generalized tangent space with the natural inner product $\langle X+\xi,Y+\eta\rangle=\tfrac12(\xi(Y)+\eta(X))$. A **generalized almost complex structure** is a real linear map $\mathcal J$ of $T\oplus T^*$ with $\mathcal J^2=-\mathrm{Id}$ and $\langle\mathcal J u,\mathcal J v\rangle=\langle u,v\rangle$; its $\sqrt{-1}$-eigenbundle is $L=\{v\in(T\oplus T^*)\otimes\mathbb C:\mathcal Jv=\sqrt{-1}\,v\}$.
--
--   **Formalization Note** The statement is fiberwise: $T\oplus T^*$ is the coordinate space `GIdx N → ℝ` (vector part on `Sum.inl`, one-form part on `Sum.inr`), endomorphisms are matrices indexed by `GIdx N`, and the complexification is `GIdx N → ℂ` with the real matrix acting through the coercion $\mathbb R\to\mathbb C$. All notions are those of the shared definition file `Definitions.Def_GeneralizedComplex_Basic`.
-- source:
--   Wikipedia, "Generalized complex structure", revision oldid=1288019306, https://en.wikipedia.org/w/index.php?title=Generalized_complex_structure&oldid=1288019306, section Examples > Symplectic manifolds, last paragraph

import Definitions.Def_GeneralizedComplex_Basic

open Matrix

namespace GeneralizedComplex

theorem eq_bShift_symplecticGen_of_genType_eq_zero {N : ℕ} (J : Matrix (GIdx N) (GIdx N) ℝ)
    (hJ : IsGenAlmostComplex J) (h0 : genType (plusIEigenspace J) = 0) :
    ∃ B ω : Matrix (Fin N) (Fin N) ℝ, Bᵀ = -B ∧ ωᵀ = -ω ∧ ω.det ≠ 0 ∧
      J = bShift B * symplecticGen ω * bShift (-B) := by sorry

end GeneralizedComplex
