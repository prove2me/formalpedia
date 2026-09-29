-- Prove2me | Theorems.Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq
-- name    : HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/e48f124e-d7ec-5a77-b5d7-da9a10087554
-- title:
--   Factorisation of a bialgebra map through a finite flat Hopf algebra
-- statement:
--   Let $R$ be a commutative ring that is a domain and a principal ideal ring, let $H$ be a commutative ring carrying the structure of a Hopf algebra over $R$ which is finite as an $R$-module, and let $H'$ be a commutative ring carrying the structure of a Hopf algebra over $R$ which is flat as an $R$-module, with $H$ and $H'$ in the same universe. Let $\varphi \colon H \to H'$ be a homomorphism of $R$-bialgebras (an $R$-algebra map compatible with comultiplication and counit). The assertion is that there exist a type $Q$ in that universe, a commutative ring structure on $Q$, a Hopf algebra structure on $Q$ over $R$ for which $Q$ is both finite and flat as an $R$-module, and bialgebra homomorphisms $\pi \colon H \to Q$ and $\iota \colon Q \to H'$ such that $\pi$ is surjective, $\iota$ is injective, and the composite of $\pi$ followed by $\iota$ equals $\varphi$. Note that the Hopf algebra structure on $Q$ is part of the existential data, so in particular an antipode on $Q$ compatible with $\pi$ and $\iota$ is produced.
--
--   This is the algebraic form of the schematic image of a homomorphism of affine group schemes over a principal ideal domain: $Q$ plays the role of the coordinate ring of the image of $\operatorname{Spec} H' \to \operatorname{Spec} H$, finite and flat (hence free) over $R$ because it embeds in $H'$ as a finitely generated torsion-free module. It is used in the study of finite flat group schemes over discrete valuation rings, for instance in producing exact sequences of Hopf algebras, in Cartier duality computations, and in the analysis of the Frobenius and Verschiebung maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_surjective_injective_comp_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem HopfAlgebra.exists_hopfAlgebra_surjective_injective_comp_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Flat R H']
    (φ : H →ₐc[R] H') :
    ∃ (Q : Type v) (_ : CommRing Q) (_ : HopfAlgebra R Q) (_ : Module.Finite R Q) (_ : Module.Flat R Q)
      (π : H →ₐc[R] Q) (ι : Q →ₐc[R] H'),
      Function.Surjective π ∧ Function.Injective ι ∧ ι.comp π = φ := by sorry
