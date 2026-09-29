-- Prove2me | Theorems.Thm_FreyPackage_frobeniusPowerDense_inf_of_restrictionKer_le
-- name    : FreyPackage.frobeniusPowerDense_inf_of_restrictionKer_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/1ddc3ab5-dfc4-5cd6-ad37-c4fe23a625b9
-- title:
--   Frobenius-power density of kerρ∩ H₂ over a Galois base field
-- statement:
--   Let $F$ be a number field that is Galois over $\mathbb{Q}$, realised as a subfield of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` compatibly with the $\mathbb{Q}$-structure. Let $M$ be a type with a multiplication and a unit, let $\rho_{\mathrm{mat}} \colon \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to M$ be a monoid homomorphism on the group of $\mathbb{Q}$-algebra automorphisms of $\overline{\mathbb{Q}}$, and let $H_2$ be a subgroup of that group. Assume that the kernel of the restriction homomorphism $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \operatorname{Gal}(F/\mathbb{Q})$, i.e. $\operatorname{Gal}(\overline{\mathbb{Q}}/F)$, is contained in $\ker \rho_{\mathrm{mat}}$ and also in $H_2$. Then for every finite set $S_\rho$ of natural numbers the subgroup $\ker\rho_{\mathrm{mat}} \sqcap H_2$ is Frobenius-power dense away from $S_\rho$: for each $\sigma \in \operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ there are a natural number $\ell$, a valuation subring $A \subseteq \overline{\mathbb{Q}}$, automorphisms $\tau, g$ and a natural number $n$ such that $\ell$ is prime, $\ell \notin S_\rho$, the image of $\ell$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$, $\tau$ lies in the decomposition subgroup of $A$ over $\mathbb{Q}$ and acts on the residue field of $A$ by $x \mapsto x^{\ell}$, and $g\,\tau^{n}\,g^{-1}\,\sigma^{-1} \in \ker\rho_{\mathrm{mat}} \sqcap H_2$.
--
--   This is the Chebotarev-type input used when a mod-$\mathfrak{m}$ matrix representation and a stabiliser subgroup both factor through a common finite Galois layer $\operatorname{Gal}(F/\mathbb{Q})$: their intersection is then still large enough that every Galois element is, modulo it, a conjugate of a power of a Frobenius element at a prime outside any prescribed finite set. It is cited in the construction of Galois-stable submodules and quotients of Hecke torsion in $J_0$, and in the decomposition of the mod-$p$ representation attached to a Weierstrass curve under a Frobenius quadraticity hypothesis.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_frobeniusPowerDense_inf_of_restrictionKer_le.lean

import Mathlib
import Definitions.Def_GaloisRep_FrobeniusPowerDense

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.frobeniusPowerDense_inf_of_restrictionKer_le (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    [Algebra F (AlgebraicClosure ℚ)] [IsScalarTower ℚ F (AlgebraicClosure ℚ)]
    {M : Type*} [MulOneClass M] (ρmat : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* M)
    (H₂ : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hρ : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρmat.ker)
    (hH : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H₂) (Sρ : Finset ℕ) :
    FrobeniusPowerDense Sρ (ρmat.ker ⊓ H₂) := by sorry
