-- Prove2me | Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
-- name    : HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/bbe87484-1857-5970-8134-fe8da90bf029
-- title:
--   Factorisation of a bialgebra map through a finite flat Hopf quotient
-- statement:
--   Let $R$ be a commutative ring that is a domain and a principal ideal ring, let $H$ be a commutative ring carrying the structure of a Hopf algebra over $R$ which is finite as an $R$-module, let $H'$ be a commutative ring carrying the structure of a Hopf algebra over $R$ which is flat as an $R$-module, and let $\varphi \colon H \to H'$ be a homomorphism of $R$-bialgebras. The assertion is that there exist a type $Q$ in the universe of $H$, a commutative ring structure on $Q$, a Hopf algebra structure on $Q$ over $R$ making $Q$ both finite and flat as an $R$-module, and bialgebra homomorphisms $\pi \colon H \to Q$ and $\iota \colon Q \to H'$ over $R$, such that $\pi$ is surjective, $\iota$ is injective, and the composite of $\pi$ followed by $\iota$ equals $\varphi$; moreover the $R$-subalgebra range of $\varphi$ is stable under the Hopf structure of $H'$ in the following two senses: for every $x$ in the range of $\varphi$, the comultiplication $\Delta(x) \in H' \otimes_R H'$ lies in the $R$-span of the set of tensors $a \otimes b$ with $a$ and $b$ in the range of $\varphi$, and the antipode $S(x)$ again lies in the range of $\varphi$.
--
--   This is the Hopf-algebraic form of the statement that a homomorphism of affine group schemes with finite flat source factors as a faithfully flat quotient followed by a closed immersion, the scheme-theoretic image being a finite flat subgroup scheme; the two final clauses record that the image of $\varphi$ is a Hopf subalgebra of $H'$. The version here places $H$ and $H'$ in independent universes, with $Q$ in the universe of $H$, and is used in the finite flat group scheme and Dieudonné module parts of the argument, for instance in the computation of ranks across the kernel of the counit and in the reduction of Hopf algebras over $\mathbb{Z}/p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

open scoped TensorProduct

theorem HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq_and_comul_mem_and_antipode_mem
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {H' : Type w} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ : H →ₐc[R] H') :
    ∃ (Q : Type v) (_ : CommRing Q) (_ : HopfAlgebra R Q) (_ : Module.Finite R Q) (_ : Module.Flat R Q)
      (π : H →ₐc[R] Q) (ι : Q →ₐc[R] H'),
      Function.Surjective π ∧ Function.Injective ι ∧ ι.comp π = φ ∧
      (∀ x ∈ (φ : H →ₐ[R] H').range, Coalgebra.comul (R := R) x ∈
        Submodule.span R {t : H' ⊗[R] H' |
          ∃ a ∈ (φ : H →ₐ[R] H').range, ∃ b ∈ (φ : H →ₐ[R] H').range, t = a ⊗ₜ[R] b}) ∧
      (∀ x ∈ (φ : H →ₐ[R] H').range, HopfAlgebra.antipode R x ∈ (φ : H →ₐ[R] H').range) := by sorry
