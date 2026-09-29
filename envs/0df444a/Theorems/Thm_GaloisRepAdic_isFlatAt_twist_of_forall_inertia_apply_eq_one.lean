-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one
-- name    : GaloisRepAdic.isFlatAt_twist_of_forall_inertia_apply_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/4fad5d5e-ce67-52de-ad35-06351a248f87
-- title:
--   Unramified twists preserve finite flatness at p
-- statement:
--   Let $A$ be a commutative local ring, $p$ an odd prime (i.e. $p \neq 2$), and $\rho$ a two-dimensional adic Galois representation over $A$: a type $V$ that is a finite free $A$-module with $\operatorname{rank}_A V = 2$, together with a monoid homomorphism $\rho$ from $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q) = \overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ to $\operatorname{End}_A V$ which is adically continuous, meaning that for every $n$ there is a finite subextension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ such that $\rho(\sigma)v - v \in \mathfrak m^n V$ for all $v$ and all $\sigma$ fixing $L$ pointwise, $\mathfrak m$ being the maximal ideal of $A$. Let $\chi \colon \operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q) \to A^\times$ be a character which is adically continuous in the corresponding sense ($\chi(\sigma) - 1 \in \mathfrak m^n$ for $\sigma$ fixing a suitable finite subextension), and assume $\chi$ is unramified above $p$: for every valuation subring $P$ of $\overline{\mathbb Q}$ whose maximal ideal contains $p$ (`LiesOverPrime`), $\chi$ is trivial on the image in $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of $P$ over $\mathbb Q$. Assume finally that $\rho$ is flat at $p$: the residue field of $A$ is finite, and for every ideal $I \subseteq A$ with $A/I$ finite there exist a commutative ring $H$ carrying a Hopf algebra structure over the subring $\mathbb Z_{(p)} \subset \mathbb Q$ of rationals whose denominator is coprime to $p$, finite and flat as a $\mathbb Z_{(p)}$-module and with cocommutative comultiplication, and a bijection $e$ from the $\mathbb Z_{(p)}$-algebra homomorphisms $H \to \overline{\mathbb Q}$ (with their convolution multiplication) onto $V/IV$ carrying the convolution product to addition and intertwining Galois conjugation of points with the induced action of $\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on $V/IV$. Then the twist $\rho \otimes \chi$, acting on the same module by $\sigma \mapsto \chi(\sigma)\rho(\sigma)$, is again flat at $p$ in this sense.
--
--   This is the standard insensitivity of finite flatness at $p$ to twisting by a character unramified at $p$, here in a global formulation: finite flat models are taken over $\mathbb Z_{(p)}$ together with a Galois-equivariant identification of their $\overline{\mathbb Q}$-points with the finite level quotients $V/IV$. It is used in the construction of the flat two-dimensional representations attached to cusp forms, through [`CuspForm.TWLevel.exists_galoisRepAdic_moduleEnd_ML_flat`](thm.html#CuspForm.TWLevel.exists_galoisRepAdic_moduleEnd_ML_flat).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_twist_of_forall_inertia_apply_eq_one.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Twist

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.isFlatAt_twist_of_forall_inertia_apply_eq_one
    {A : Type} [CommRing A] [IsLocalRing A] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (ρ : GaloisRepAdic A) (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hχ : GaloisCharIsAdicContinuous A χ)
    (hunr : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (hflat : ρ.IsFlatAt p) :
    (ρ.twist χ hχ).IsFlatAt p := by sorry
