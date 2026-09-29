-- Prove2me | Theorems.Thm_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
-- name    : HopfAlgebra.exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/f8ed9615-a358-5883-9d9f-a3d8d32b2c5d
-- title:
--   Every K-point kernel is a translate of the augmentation ideal
-- statement:
--   Let $K$ be a field and let $A$ be a commutative ring carrying the structure of a Hopf algebra over $K$, and let $\chi \colon A \to K$ be a homomorphism of $K$-algebras. The assertion is that there exists a $K$-algebra automorphism $e$ of $A$ such that the preimage under (the ring homomorphism underlying) $e$ of the kernel of the counit $\varepsilon =$ `Bialgebra.counitAlgHom K A`, i.e. of the augmentation ideal $I = \ker \varepsilon \subseteq A$, is exactly the kernel of $\chi$: in symbols $e^{-1}(I) = \ker \chi$ as ideals of $A$, the kernels being taken of the underlying ring homomorphisms. No finiteness, characteristic or nontriviality hypothesis on $A$ is imposed; the statement asserts only existence of such an automorphism and does not name one, so no formula for $e$ (such as right translation by $\chi$) is part of the conclusion.
--
--   This is the Hopf-algebra statement that right translation by a $K$-point carries the augmentation ideal to the kernel of that point, so that all kernels of $K$-algebra homomorphisms $A \to K$ are equivalent under the automorphism group of $A$. It is used in the proof that the localisation of a finite-type Hopf algebra over a field of characteristic zero at the prime given by the kernel of such a homomorphism is a domain, a step in Cartier's theorem on the regularity of such Hopf algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
    (K : Type*) [Field K]
    (A : Type*) [CommRing A] [HopfAlgebra K A] (χ : A →ₐ[K] K) :
    ∃ e : A ≃ₐ[K] A,
      (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap e.toRingEquiv.toRingHom
        = RingHom.ker χ.toRingHom := by sorry
