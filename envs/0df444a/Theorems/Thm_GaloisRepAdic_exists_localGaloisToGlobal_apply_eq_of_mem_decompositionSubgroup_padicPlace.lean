-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace
-- name    : GaloisRepAdic.exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/f9868340-70d5-595a-bc4b-36f58d7ff595
-- title:
--   Decomposition elements act through local Galois elements
-- statement:
--   Let $B$ be a finite commutative local ring, let $p$ be a prime, and let $\rho$ be an element of [`GaloisRepAdic B`](def/GaloisRep_Adic.html#L16): that is, a type $V$ carrying an abelian group structure and a $B$-module structure which is free and finite over $B$ with $\operatorname{rank}_B V = 2$, a monoid homomorphism $\rho.\rho$ from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\operatorname{End}_B(V)$, and the $\mathfrak{m}$-adic continuity condition that for every $n$ there is an intermediate field $L$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that every automorphism fixing $L$ pointwise satisfies $\rho.\rho(\tau)v-v \in (\mathfrak{m}_B^n)\cdot V$ for all $v \in V$. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ lying in the decomposition subgroup over $\mathbb{Q}$ of the valuation subring [`padicPlace p`](def/GaloisRep_CompletionBridge.html#L25), the pullback of the unit ball of the valuation on $\mathrm{PadicAlgCl}\ p$ along a fixed $\mathbb{Q}$-algebra embedding $\mathrm{AlgebraicClosure}\ \mathbb{Q} \to \mathrm{PadicAlgCl}\ p$. Then there exists a $\mathbb{Q}_p$-algebra automorphism $g$ of $\mathrm{PadicAlgCl}\ p$ with $\rho.\rho(\mathrm{localGaloisToGlobal}\ p\ g) = \rho.\rho(\sigma)$, where [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) sends $g$ to the restriction of $g$, viewed as a $\mathbb{Q}$-algebra automorphism, to the normal subextension $\mathrm{AlgebraicClosure}\ \mathbb{Q}$. The conclusion is an equality of endomorphisms of $V$, not of Galois elements.
--
--   This is the bridge allowing assertions about the restriction of a two-dimensional $\mathfrak{m}$-adically continuous global representation with finite coefficient ring to the decomposition group at the chosen place above $p$ to be read off on the genuine local Galois group $\mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$, where local constructions such as Kummer theory are available. It is used in the analysis of the action of inertia at $p$ on the representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.exists_localGaloisToGlobal_apply_eq_of_mem_decompositionSubgroup_padicPlace
    {B : Type} [CommRing B] [IsLocalRing B] [Finite B] (p : ℕ) [Fact p.Prime] (ρ : GaloisRepAdic B)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ (padicPlace p).decompositionSubgroup ℚ) :
    ∃ g : (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p), ρ.ρ (localGaloisToGlobal p g) = ρ.ρ σ := by sorry
