-- Prove2me | Theorems.Thm_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
-- name    : KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/2ed7556f-6c34-5571-a75e-be1b30c85403
-- title:
--   Base change of differentials along a surjection
-- statement:
--   Let $R$, $C$, $A$, $R'$ be commutative rings in a single universe, with $C$ and $A$ algebras over $R$, $A$ an algebra over $C$ compatible with the maps from $R$ (a scalar tower $R \to C \to A$), and suppose the structure map $C \to A$ is surjective. Let $R'$ be an algebra over both $A$ and $C$, forming a scalar tower $C \to A \to R'$. The assertion is that the type of $R'$-linear equivalences
--   $$R' \otimes_A \Omega_{A/R} \;\simeq\; \bigl(R' \otimes_C \Omega_{C/R}\bigr)\big/ \operatorname{span}_{R'}\Bigl\{\,1 \otimes d_{C/R} f \;:\; f \in \ker(C \to A)\,\Bigr\}$$
--   is nonempty, the submodule on the right being the $R'$-span of the range of the map sending an element $f$ of the kernel ideal to $(1 : R') \otimes_C D_{C/R}(f)$. Thus the statement is the existence of such an isomorphism rather than a designated choice of one; no smoothness, finiteness or flatness hypothesis is imposed.
--
--   This is the right-exactness of base change applied to the conormal (second fundamental) exact sequence of the surjection $C \to A$: the module of differentials of the quotient, pulled back to $R'$, is the pull-back of the ambient differentials modulo the differentials of the defining ideal. It is used in the affine descent step [`NeronModelInfra.smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus`](thm.html#NeronModelInfra.smoothnessDefect_affineDilatation_add_one_le_of_isSmoothAt_of_mem_freeLocus), where taking $\Omega_{C/R}$ free turns the smoothness defect of a point into the length of the torsion of an explicit quotient of a free module, replacing the classical computation with Jacobi minors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_KaehlerDifferential_nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct KaehlerDifferential

universe u

theorem KaehlerDifferential.nonempty_baseChange_linearEquiv_quotient_span_tmul_D_of_surjective
    {R C A R' : Type u} [CommRing R] [CommRing C] [CommRing A] [CommRing R']
    [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
    (hsurj : Function.Surjective (algebraMap C A))
    [Algebra A R'] [Algebra C R'] [IsScalarTower C A R'] :
    Nonempty ((R' ⊗[A] Ω[A⁄R]) ≃ₗ[R']
      ((R' ⊗[C] Ω[C⁄R]) ⧸ Submodule.span R'
        (Set.range fun f : RingHom.ker (algebraMap C A) => (1 : R') ⊗ₜ[C] D R C (f : C)))) := by sorry
