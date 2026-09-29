-- Prove2me | Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer
-- name    : HopfAlgebra.exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/e36e7469-8d5f-5e5b-a6c0-a3487d405054
-- title:
--   Finite Galois modules as points of finite commutative Hopf algebras
-- statement:
--   Let $F$ and $L$ be fields with $L$ an $F$-algebra such that $L/F$ is Galois, and let $N$ be a finite additive abelian group equipped with a distributive multiplicative action of the automorphism group $L \simeq_{\mathrm{alg}[F]} L$, i.e. the Galois group acts on $N$ by group automorphisms. Assume that for every $x \in N$ the stabiliser of $x$ is an open subset of $L \simeq_{\mathrm{alg}[F]} L$ for its Krull topology; this is the continuity of the action. The conclusion asserts the existence of a type $A$ carrying a commutative ring structure and a Hopf algebra structure over $F$ such that $A$ is finite as an $F$-module and its comultiplication is cocommutative, together with a bijection $e$ from `WithConv (A →ₐ[F] L)`, the set of $F$-algebra homomorphisms $A \to L$ regarded with its convolution product coming from the comultiplication of $A$ and the multiplication of $L$, onto $N$, subject to two conditions: $e(f * g) = e(f) + e(g)$ for all $f, g$, so that $e$ transports the convolution product to the addition of $N$; and, for every $\sigma \in L \simeq_{\mathrm{alg}[F]} L$ and all $f, g$, if $g(a) = \sigma(f(a))$ for every $a \in A$, then $e(g) = \sigma \cdot e(f)$, so that $e$ is equivariant for the Galois actions.
--
--   This is the Galois-descent statement that a finite abelian group with a continuous action of $\mathrm{Gal}(L/F)$ is realised as the group of $L$-points of a finite commutative cocommutative Hopf algebra over $F$, the Hopf algebra being a form of the algebra of $L$-valued functions on $N$ with structure maps induced by the addition, zero and negation of $N$. It is used in the analysis of ordinary Galois representations, where it is cited by [`GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition`](thm.html#GaloisRep.exists_hopfAlgebra_withConv_equiv_of_ordinary_of_unitKummer_decomposition) to pass from a finite Galois module to the finite flat group scheme it defines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer.lean

import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Convolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem HopfAlgebra.exists_hopfAlgebra_withConv_equiv_of_isOpen_stabilizer
    (F L : Type) [Field F] [Field L] [Algebra F L] [IsGalois F L]
    (N : Type) [AddCommGroup N] [Finite N] [DistribMulAction (L ≃ₐ[F] L) N]
    (hN : ∀ x : N, IsOpen (MulAction.stabilizer (L ≃ₐ[F] L) x : Set (L ≃ₐ[F] L))) :
    ∃ (A : Type) (_ : CommRing A) (_ : HopfAlgebra F A),
      Module.Finite F A ∧ Coalgebra.IsCocomm F A ∧
      ∃ e : WithConv (A →ₐ[F] L) ≃ N,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : L ≃ₐ[F] L) (f g : WithConv (A →ₐ[F] L)),
          (∀ a : A, g a = σ (f a)) → e g = σ • e f := by sorry
