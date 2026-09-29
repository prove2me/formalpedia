-- Prove2me | Theorems.Thm_HopfAlgebra_bijective_baseChange_of_hasFVectDevissage
-- name    : HopfAlgebra.bijective_baseChange_of_hasFVectDevissage
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/98aa3eb8-9281-5e55-a954-8fa3cd45dd36
-- title:
--   Bijectivity of R₂⊗φ from an F-vector dévissage
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, let $p$ be a prime with $p \neq 2$, and let $H$, $H'$ be commutative Hopf algebras over $R$ that are finite and flat as $R$-modules and whose comultiplications are cocommutative. Let $\varphi \colon H \to H'$ be a morphism of $R$-bialgebras whose underlying $R$-linear map becomes bijective after base change to $K$. Let $R_2$ be a further discrete valuation domain, an $R$-algebra that is faithfully flat over $R$, with fraction field $K_2$, and assume $p$ is irreducible in $R_2$. Assume finally that the $K_2$-Hopf algebra $K_2 \otimes_{R_2} (R_2 \otimes_R H')$ satisfies the inductive predicate [`HopfAlgebra.HasFVectDevissage`](def/HopfAlgebra_HasFVectDevissage.html#L10) for the data $(R_2, K_2, p)$: it is obtained from the case of $K_2$-rank $1$ by finitely many steps, each consisting of a surjective bialgebra map $\pi \colon A \to \bar A$ of finite cocommutative $K_2$-Hopf algebras with $\bar A$ already admitting such a dévissage, together with a finite field $F$ of cardinality $p^r$ ($r \neq 0$) with $p^r - 1$ a unit of $R_2$, a character $\chi \colon F^\times \to R_2^\times$ lifting a ring embedding $\iota \colon F \to$ the residue field of $R_2$, the equality $\dim_{K_2} \mathrm{hopfKer}(\pi) = p^r$ (the Hopf kernel being the equaliser of the coaction of $\pi$ and $a \mapsto a \otimes 1$), and an $F$-vector structure on $\mathrm{hopfKer}(\pi)$, i.e. a map $a \mapsto \mathrm{act}(a)$ from $F$ to bialgebra endomorphisms with $\mathrm{act}(1) = \mathrm{id}$, $\mathrm{act}(ab) = \mathrm{act}(a) \circ \mathrm{act}(b)$, $\mathrm{act}(0)$ the unit of the convolution algebra and $\mathrm{act}(a+b) = \mathrm{act}(a) * \mathrm{act}(b)$ for convolution. Then the base change of $\varphi$ along $R \to R_2$, as an $R_2$-linear map $R_2 \otimes_R H \to R_2 \otimes_R H'$, is bijective.
--
--   This is the identification step in Raynaud's proof that a generically bijective morphism of finite flat commutative cocommutative Hopf algebras over a discrete valuation ring is bijective, carried out over an extension base $R_2$ on which a dévissage by $F$-vector group schemes is available; the existence of such $R_2$ and of the dévissage, and the descent back to $R$, are separate steps. It feeds the simplicity/surjectivity statement [`HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple`](thm.html#HopfAlgebra.surjective_of_injective_of_surjective_baseChange_of_pow_eq_one_of_simple).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_bijective_baseChange_of_hasFVectDevissage.lean

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_HasFVectDevissage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open scoped TensorProduct

theorem HopfAlgebra.bijective_baseChange_of_hasFVectDevissage
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {H : Type v} [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Flat R H]
    [Coalgebra.IsCocomm R H]
    {H' : Type v} [CommRing H'] [HopfAlgebra R H'] [Module.Finite R H'] [Module.Flat R H']
    [Coalgebra.IsCocomm R H']
    (φ : H →ₐc[R] H') (hφK : Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange K))
    (R₂ : Type u) [CommRing R₂] [IsDomain R₂] [IsDiscreteValuationRing R₂] [Algebra R R₂]
    [Module.FaithfullyFlat R R₂]
    (K₂ : Type u) [Field K₂] [Algebra R₂ K₂] [IsFractionRing R₂ K₂]
    (hunif₂ : Irreducible (p : R₂))
    (hdev : HopfAlgebra.HasFVectDevissage R₂ K₂ p (K₂ ⊗[R₂] (R₂ ⊗[R] H'))) :
    Function.Bijective ((φ : H →ₐ[R] H').toLinearMap.baseChange R₂) := by sorry
