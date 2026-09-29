-- Prove2me | Theorems.Thm_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp
-- name    : HopfAlgebra.comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/6227e964-18f7-5746-8e70-071a2a371863
-- title:
--   Naturality of the Verschiebung pinned on the Cartier dual
-- statement:
--   Let $p$ be a prime, and let $B$ and $C$ be commutative rings carrying Hopf algebra structures over $\mathbb{Z}/p$ whose comultiplications are cocommutative and which are finite as $\mathbb{Z}/p$-modules. Let $q \colon B \to C$ be a bialgebra homomorphism over $\mathbb{Z}/p$. Write [`CartierDual (ZMod p) B`](def/HopfAlgebra_CartierDual.html#L12) for the $\mathbb{Z}/p$-linear dual $\mathrm{Hom}_{\mathbb{Z}/p}(B,\mathbb{Z}/p)$ of $B$, equipped with the ring structure dual to the Hopf algebra structure of $B$ (so that powers $\varphi^p$ of a functional are formed by convolution), and likewise for $C$. Assume given bialgebra endomorphisms $V_B \colon B \to B$ and $V_C \colon C \to C$ over $\mathbb{Z}/p$ which are pinned by the conditions $\varphi(V_B b) = (\varphi^p)(b)$ for all $\varphi \in$ [`CartierDual (ZMod p) B`](def/HopfAlgebra_CartierDual.html#L12) and all $b \in B$, and $\psi(V_C c) = (\psi^p)(c)$ for all $\psi \in$ [`CartierDual (ZMod p) C`](def/HopfAlgebra_CartierDual.html#L12) and all $c \in C$. The conclusion is the equality of bialgebra homomorphisms $B \to C$ given by $V_B$ followed by $q$ and by $q$ followed by $V_C$, i.e. $q \circ V_B = V_C \circ q$.
--
--   This is the naturality (functoriality) of the Verschiebung of a finite commutative cocommutative Hopf algebra in characteristic $p$, in the formulation in which $V$ is characterised as the transpose of the $p$-power Frobenius of the Cartier dual. It is used in the treatment of the $p$-divisible group attached to the Néron model of the Jacobian at $p$, where the Verschiebung must be transported along maps of Hopf algebras (for instance along a quotient, and in the Hopf-algebra form of the Eichler–Shimura relation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp
    (p : ℕ) [Fact p.Prime]
    {B : Type} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B] [Module.Finite (ZMod p) B]
    {C : Type} [CommRing C] [HopfAlgebra (ZMod p) C] [Coalgebra.IsCocomm (ZMod p) C] [Module.Finite (ZMod p) C]
    (q : B →ₐc[ZMod p] C)
    (VB : B →ₐc[ZMod p] B) (hVB : ∀ (φ : CartierDual (ZMod p) B) (b : B), φ (VB b) = (φ ^ p) b)
    (VC : C →ₐc[ZMod p] C) (hVC : ∀ (φ : CartierDual (ZMod p) C) (c : C), φ (VC c) = (φ ^ p) c) :
    q.comp VB = VC.comp q := by sorry
