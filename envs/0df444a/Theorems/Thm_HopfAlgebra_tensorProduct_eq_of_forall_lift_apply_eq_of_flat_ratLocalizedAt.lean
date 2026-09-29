-- Prove2me | Theorems.Thm_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt
-- name    : HopfAlgebra.tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/5d88a672-cf95-587d-86f1-fd65f9b9f631
-- title:
--   Pairs of ℚ̄-points separate H⊗ H
-- statement:
--   Fix a natural number $p$ and write $R =$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb Q$ consisting of those rationals whose denominator (in lowest terms) is coprime to $p$; for $p$ prime this is the localisation $\mathbb Z_{(p)}$. Let $H$ be a commutative ring carrying the structure of a Hopf algebra over $R$, and assume that $H$ is finite as an $R$-module and flat as an $R$-module. Let $a$ and $b$ be two elements of $H \otimes_R H$, and suppose that for every pair $f, g$ of $R$-algebra homomorphisms $H \to \overline{\mathbb Q}$ (the algebraic closure of $\mathbb Q$) the induced algebra homomorphism $H \otimes_R H \to \overline{\mathbb Q}$ obtained from the commuting pair $(f,g)$ by `Algebra.TensorProduct.lift`, that is $x \otimes y \mapsto f(x) g(y)$, takes the same value on $a$ as on $b$. The conclusion is that $a = b$. Thus the $\overline{\mathbb Q}$-valued points of $H \otimes_R H$ arising from pairs of $\overline{\mathbb Q}$-valued points of $H$ separate the elements of $H \otimes_R H$.
--
--   This is the two-variable form of the statement that, for a finite flat commutative Hopf algebra over $\mathbb Z_{(p)}$, elements are detected by their values at $\overline{\mathbb Q}$-points. It is used to verify identities in $H \otimes_R H$ pointwise, in particular in the compatibility of the comultiplication of a finite flat model with a Hecke endomorphism ([`ModularCurve.finiteFlatModel_comul_comp_heckeEndo`](thm.html#ModularCurve.finiteFlatModel_comul_comp_heckeEndo)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct in

theorem HopfAlgebra.tensorProduct_eq_of_forall_lift_apply_eq_of_flat_ratLocalizedAt
    (p : ℕ) (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    (a b : H ⊗[GaloisRep.ratLocalizedAt p] H)
    (hab : ∀ f g : H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ,
      Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) a =
        Algebra.TensorProduct.lift f g (fun _ _ => .all _ _) b) :
    a = b := by sorry
