-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
-- name    : HopfAlgebra.exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/e8951f7e-02bc-5d63-b4d0-5390924c26a8
-- title:
--   Existence of bialgebra lifts to R[M] over henselian local rings
-- statement:
--   Let $R$ be a commutative ring that is a henselian local ring, with residue field $\kappa =$ `ResidueField R`, and let $H$ be a commutative ring carrying a Hopf algebra structure over $R$ whose underlying $R$-module is finite and flat and whose comultiplication is cocommutative; $R$ and $H$ lie in the same universe. Let $M$ be a finite additive commutative group, so that `AddMonoidAlgebra R M` is the group algebra $R[M]$. Given a homomorphism $\psi_0 \colon \kappa \otimes_R H \to \kappa[M]$ of bialgebras over $\kappa$ (a `BialgHom`, i.e. simultaneously an algebra and a coalgebra homomorphism), the assertion is that there exists a bialgebra homomorphism $\psi \colon H \to R[M]$ over $R$ such that, as $R$-algebra homomorphisms $H \to \kappa[M]$, the composite of the underlying algebra map of $\psi$ with the coefficient-change map $R[M] \to \kappa[M]$ induced by the residue map $R \to \kappa$ agrees with the composite of the inclusion $H \to \kappa \otimes_R H$, $x \mapsto 1 \otimes x$, followed by $\psi_0$ regarded as an $R$-algebra homomorphism by restriction of scalars. Only the existence of such a $\psi$ is asserted, not its uniqueness.
--
--   In the dual language of group schemes this is the surjectivity half of the statement that homomorphisms from the split diagonalisable group $D(M) = \operatorname{Spec} R[M]$ into the finite flat commutative group scheme $\operatorname{Spec} H$ lift from the special fibre over a henselian local base. Combined with the corresponding uniqueness statement over an arbitrary local ring, it yields the bijectivity result [`HopfAlgebra.existsUnique_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing`](thm.html#HopfAlgebra.existsUnique_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing
open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_addMonoidAlgebra_lift_residueField_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {H : Type u} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H] [Coalgebra.IsCocomm R H]
    (M : Type v) [AddCommGroup M] [Finite M]
    (ψ₀ : ResidueField R ⊗[R] H →ₐc[ResidueField R] AddMonoidAlgebra (ResidueField R) M) :
    ∃ ψ : H →ₐc[R] AddMonoidAlgebra R M,
      (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp (ψ : H →ₐ[R] AddMonoidAlgebra R M) =
        ((ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] AddMonoidAlgebra (ResidueField R) M).restrictScalars R).comp
          Algebra.TensorProduct.includeRight := by sorry
