-- Prove2me | Theorems.Thm_HopfAlgebra_exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
-- name    : HopfAlgebra.exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/d30beaca-d94b-5188-8882-79f865f1453d
-- title:
--   Identity-component Hopf quotient over a henselian local base
-- statement:
--   Let $p$ be a prime and let $O$ be a commutative ring that is a henselian local ring, equipped with $O$-algebra structures on $\overline{\mathbb Q}$ (the algebraic closure of $\mathbb Q$) and on $\mathbb Z/p$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$, and assume: the image of every $x \in O$ in $\overline{\mathbb Q}$ lies in $P$; every $x$ in the maximal ideal of $O$ has $P$-valuation of its image $<1$; and the structure map $O \to \mathbb Z/p$ has kernel exactly the maximal ideal of $O$. Let $C$ be a commutative ring which is a Hopf algebra over $O$, cocommutative as an $O$-coalgebra, and finite and free as an $O$-module. The assertion is the existence of a commutative ring $C_0$ carrying a Hopf $O$-algebra structure, cocommutative, finite and free over $O$, together with a surjective $O$-bialgebra map $q_0 : C \to C_0$, such that: (i) $(\mathbb Z/p) \otimes_O C_0$ is a local ring; (ii) every $O$-algebra map $f : C \to \overline{\mathbb Q}$ with $P$-valuation of $f(c) - \varepsilon(c)$ less than $1$ for all $c \in C$, where $\varepsilon$ is the counit, factors as $f = g \circ q_0$ for some $O$-algebra map $g : C_0 \to \overline{\mathbb Q}$; (iii) for every local ring $L$ that is an $O$-algebra with local structure map $O \to L$, every $O$-algebra map $f : C \to L$ with $f(c) - \varepsilon(c)$ in the maximal ideal of $L$ for all $c$ factors as $f = g \circ q_0$ for some $O$-algebra map $g : C_0 \to L$; and (iv) for every $O$-bialgebra endomorphism $\varphi$ of $C$ there is a unique $O$-bialgebra endomorphism $\psi$ of $C_0$ with $\psi \circ q_0 = q_0 \circ \varphi$. Only existence of $C_0$ and $q_0$ is asserted, and in (ii) and (iii) only existence of the factoring map $g$; no uniqueness or minimality of the pair $(C_0, q_0)$ is claimed.
--
--   In geometric language this produces the identity component $N^0 \subset N$ of a finite flat commutative group scheme $N$ over a henselian local base as a Hopf algebra quotient $C \to C_0$ of the coordinate ring, characterised by the property that all points congruent to the identity, over $\overline{\mathbb Q}$ with respect to a place $P$ or over any local $O$-algebra, factor through it, and that endomorphisms of $N$ descend to it. It feeds the factorisation of points of $p$-divisible groups through the identity component used in the study of the Galois representations attached to the Frey curve; the proof uses the decomposition of a module-finite algebra over a henselian local ring into local factors by a complete family of orthogonal idempotents indexed by its maximal spectrum.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing.lean

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem HopfAlgebra.exists_bialgHom_surjective_isLocalRing_tensorProduct_forall_point_comp_eq_of_henselianLocalRing
    (p : ℕ) [Fact p.Prime]
    (O : Type) [CommRing O] [HenselianLocalRing O]
    [Algebra O (AlgebraicClosure ℚ)] [Algebra O (ZMod p)]
    (P : ValuationSubring (AlgebraicClosure ℚ))
    (hOP : ∀ x : O, algebraMap O (AlgebraicClosure ℚ) x ∈ P)
    (hloc : ∀ x : O, x ∈ IsLocalRing.maximalIdeal O →
      P.valuation (algebraMap O (AlgebraicClosure ℚ) x) < 1)
    (hres : ∀ x : O, algebraMap O (ZMod p) x = 0 ↔ x ∈ IsLocalRing.maximalIdeal O)
    (C : Type) [CommRing C] [HopfAlgebra O C] [Coalgebra.IsCocomm O C]
    [Module.Finite O C] [Module.Free O C] :
    ∃ (C₀ : Type) (_ : CommRing C₀) (_ : HopfAlgebra O C₀) (_ : Coalgebra.IsCocomm O C₀)
      (_ : Module.Finite O C₀) (_ : Module.Free O C₀)
      (q₀ : C →ₐc[O] C₀),
      Function.Surjective q₀ ∧

      IsLocalRing (ZMod p ⊗[O] C₀) ∧

      (∀ f : C →ₐ[O] AlgebraicClosure ℚ,
        (∀ c : C, P.valuation (f c - algebraMap O (AlgebraicClosure ℚ) (Coalgebra.counit c)) < 1) →
        ∃ g : C₀ →ₐ[O] AlgebraicClosure ℚ, f = g.comp (q₀ : C →ₐ[O] C₀)) ∧

      (∀ (L : Type) [CommRing L] [IsLocalRing L] [Algebra O L], IsLocalHom (algebraMap O L) →
        ∀ f : C →ₐ[O] L, (∀ c : C, f c - algebraMap O L (Coalgebra.counit c) ∈ IsLocalRing.maximalIdeal L) →
        ∃ g : C₀ →ₐ[O] L, f = g.comp (q₀ : C →ₐ[O] C₀)) ∧

      (∀ φ : C →ₐc[O] C, ∃! ψ : C₀ →ₐc[O] C₀, ψ.comp q₀ = q₀.comp φ) := by sorry
