-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp
-- name    : HopfAlgebra.exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/2f116e8c-68ec-5641-9c98-6024638839ca
-- title:
--   Reduced Cartier dual makes Verschiebung a bialgebra automorphism
-- statement:
--   Let $p$ be a prime and let $A$ be a commutative ring carrying a Hopf algebra structure over $\mathbb{Z}/p$ whose comultiplication is cocommutative, and which is finite and free as a $\mathbb{Z}/p$-module. Write $\mathrm{CartierDual}\,(\mathbb{Z}/p)\,A$ for the Cartier dual, that is, the $\mathbb{Z}/p$-linear dual $\operatorname{Hom}_{\mathbb{Z}/p}(A,\mathbb{Z}/p)$ equipped with the bialgebra structure dual to that of $A$ (so that multiplication of functionals is convolution through the comultiplication of $A$). Assume the commutative ring underlying this Cartier dual is reduced. Then there exists a bialgebra isomorphism $V : A \to A$ over $\mathbb{Z}/p$ such that for every functional $\chi$ in the Cartier dual, the image of $\chi$ under [`CartierDual.map`](def/HopfAlgebra_CartierDualMap.html#L102) applied to the bialgebra homomorphism underlying $V$ — i.e. the transpose $\chi \mapsto \chi \circ V$, viewed as a bialgebra endomorphism of the Cartier dual — equals $\chi^{p}$, the $p$-th power of $\chi$ in the Cartier dual. Thus $V$ is an automorphism of $A$ whose transpose is the Frobenius of the dual algebra.
--
--   This is the statement that a finite commutative cocommutative Hopf algebra over $\mathbb{F}_p$ with reduced Cartier dual (i.e. of multiplicative type) has bijective Verschiebung: the endomorphism pinned down by the requirement that its transpose be the $p$-power map on the dual is an automorphism. It is used in the project in establishing multiplicativity statements for finite Hopf algebras arising from the torus quotient of the finite part of a Néron object attached to a modular curve, and in a criterion involving base change to a group algebra over a local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_bialgEquiv_forall_cartierDual_map_eq_pow_of_isReduced_cartierDual_zmodp
    (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A] [Module.Free (ZMod p) A]
    (hred : IsReduced (CartierDual (ZMod p) A)) :
    ∃ V : A ≃ₐc[ZMod p] A, ∀ χ : CartierDual (ZMod p) A, CartierDual.map (V : A →ₐc[ZMod p] A) χ = χ ^ p := by sorry
