-- Prove2me | Theorems.Thm_HopfAlgebra_exists_weilRestriction_of_etale
-- name    : HopfAlgebra.exists_weilRestriction_of_etale
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/cc24e85b-2306-5fe2-9c97-3240797433b5
-- title:
--   Weil restriction along a finite étale extension is finite flat
-- statement:
--   Fix a universe $u$. Let $A$ be a commutative ring and $B$ a commutative ring that is an $A$-algebra which is finite and free as an $A$-module and étale over $A$, and let $H$ be a commutative ring equipped with a Hopf algebra structure over $B$, finite and free as a $B$-module, whose comultiplication is cocommutative. The assertion is the existence of a type $W$ in the same universe, carrying a commutative ring structure and a Hopf algebra structure over $A$, such that $W$ is finite as an $A$-module, flat as an $A$-module, cocommutative as an $A$-coalgebra, and such that there is a family of bijections, one for each commutative ring $T$ with an $A$-algebra structure,
--   $$e_T : \mathrm{WithConv}\,(W \to_{\mathrm{alg}[A]} T) \;\simeq\; \mathrm{WithConv}\,(H \to_{\mathrm{alg}[B]} B \otimes_A T),$$
--   between the $A$-algebra homomorphisms $W \to T$ and the $B$-algebra homomorphisms $H \to B \otimes_A T$, both regarded through the type synonym `WithConv` which equips such Hom-sets with the convolution product coming from the Hopf structure, and this family satisfies two conditions: each $e_T$ is multiplicative for the convolution products, $e_T(fg) = e_T(f)\,e_T(g)$; and the family is natural in $T$, in the sense that for every $A$-algebra homomorphism $u : T \to T'$ and every $f : W \to_{\mathrm{alg}[A]} T$ one has $e_{T'}(u \circ f) = (\mathrm{id}_B \otimes u) \circ e_T(f)$, the composites being formed after passing between `WithConv` and the underlying Hom-sets via `WithConv.toConv` and `WithConv.ofConv`. Only multiplicativity of $e_T$ is asserted; no statement is made about units or inverses.
--
--   This is the existence of the Weil restriction $\operatorname{Res}_{B/A} G$ of a finite flat commutative group scheme $G = \operatorname{Spec} H$ along a finite free étale extension $A \to B$, in functor-of-points form: the representing Hopf algebra $W$ over $A$ is finite and flat, and its points are the $B$-points of $G$ over $B \otimes_A T$, compatibly with the group structures. It is used in the construction of finite flat models over $\mathbb{Z}_p$, being cited by [`HopfAlgebra.exists_finiteFlat_padicInt_model_pi_algHom_of_etale`](thm.html#HopfAlgebra.exists_finiteFlat_padicInt_model_pi_algHom_of_etale) and by [`HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer`](thm.html#HopfAlgebra.exists_finiteFlat_padicInt_withConv_equiv_of_multiplicative_by_unramified_of_unitKummer).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_weilRestriction_of_etale.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u

theorem HopfAlgebra.exists_weilRestriction_of_etale
    (A : Type u) [CommRing A] (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    [Algebra.Etale A B]
    (H : Type u) [CommRing H] [HopfAlgebra B H] [Module.Finite B H] [Module.Free B H] [Coalgebra.IsCocomm B H] :
    ∃ (W : Type u) (_ : CommRing W) (_ : HopfAlgebra A W),
      Module.Finite A W ∧ Module.Flat A W ∧ Coalgebra.IsCocomm A W ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra A T],
          WithConv (W →ₐ[A] T) ≃ WithConv (H →ₐ[B] (B ⊗[A] T)),
        (∀ (T : Type u) [CommRing T] [Algebra A T] (f g : WithConv (W →ₐ[A] T)),
            e T (f * g) = e T f * e T g) ∧
        ∀ (T T' : Type u) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (u : T →ₐ[A] T')
          (f : WithConv (W →ₐ[A] T)),
          e T' (WithConv.toConv (u.comp f.ofConv))
            = WithConv.toConv ((Algebra.TensorProduct.map (AlgHom.id B B) u).comp (e T f).ofConv) := by sorry
