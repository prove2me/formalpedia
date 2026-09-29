-- Prove2me | Theorems.Thm_GaloisRepAdic_exists_inertia_eigenvector_tameCharacter_of_isFlatAt
-- name    : GaloisRepAdic.exists_inertia_eigenvector_tameCharacter_of_isFlatAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/9d023549-983f-5871-b70a-333cb51f1a36
-- title:
--   Tame inertia eigenvector for a flat rank-two representation
-- statement:
--   Let $A$ be a commutative local ring and let $\rho$ be an $A$-adic Galois representation in the project's sense: a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$ together with a monoid homomorphism $\rho$ from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ to $\operatorname{End}_A V$ which is adically continuous, i.e. for each $n$ there is a finite extension $L/\mathbb Q$ inside $\overline{\mathbb Q}$ with $\rho(\sigma)v - v \in \mathfrak m_A^n\cdot V$ for all $v$ and all $\sigma$ fixing $L$ pointwise. Assume $p$ is a prime, $p \neq 2$, the image of $p$ lies in $\mathfrak m_A$, and $\rho$ is flat at $p$: the residue field of $A$ is finite, and for every ideal $I$ with $A/I$ finite there is a commutative ring $H$, a finite flat cocommutative Hopf algebra over the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$, together with a bijection from the convolution group of $\mathbb Z_{(p)}$-algebra maps $H \to \overline{\mathbb Q}$ onto $V/I\cdot V$ carrying convolution to addition and intertwining the Galois action on algebra maps with the induced action of $\rho$ on $V/I\cdot V$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a nonunit of $P$, and let $\pi \in \overline{\mathbb Q}$ satisfy $\pi^{p^2-1} = p$. Then there are a ring homomorphism $\psi_k$ from the residue field of $A$ to that of $P$ and a nonzero vector $v$ in the base change along $\psi_k$ of the residual representation $\mathrm{ResidueField}(A) \otimes_A V$ such that, writing $t = P.\mathrm{tameCharacter}\ \pi$ (so $t(\sigma)$ is the residue of $\sigma\pi/\pi$ when $\sigma\pi/\pi \in P$, and $0$ otherwise), one of the four identities $\sigma v = v$, $\sigma v = t(\sigma)\,v$, $\sigma v = t(\sigma)^p\,v$, $\sigma v = t(\sigma)^{p+1}\,v$ holds for all $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ of the inertia subgroup of the decomposition group of $P$.
--
--   This is the local analysis at $p$ of a rank-two representation arising from a finite flat group scheme: the tame inertia action on a suitable line is given by one of the four products of the two fundamental characters of level two, $1$, $t$, $t^p$, $t^{p+1}$, the last being the mod $p$ cyclotomic character on inertia. It is invoked by [`CuspForm.exists_galoisRepAdic_inertia_eigenvector_tameCharacter_of_not_isUnit_heckeT_of_ne_two`](thm.html#CuspForm.exists_galoisRepAdic_inertia_eigenvector_tameCharacter_of_not_isUnit_heckeT_of_ne_two) to constrain inertia at $p$ for representations attached to cusp forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_exists_inertia_eigenvector_tameCharacter_of_isFlatAt.lean

import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRepAdic.exists_inertia_eigenvector_tameCharacter_of_isFlatAt
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpA : (p : A) ∈ IsLocalRing.maximalIdeal A)
    (hflat : ρ.IsFlatAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {π : AlgebraicClosure ℚ} (hπ : π ^ (p ^ 2 - 1) = p) :
    ∃ (ψk : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField P)
      (v : (ρ.residual.baseChangeAlong ψk).V), v ≠ 0 ∧
      ((∀ σ ∈ P.inertiaSubgroupIn ℚ, (ρ.residual.baseChangeAlong ψk).ρ σ v = v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ.residual.baseChangeAlong ψk).ρ σ v = P.tameCharacter π σ • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ.residual.baseChangeAlong ψk).ρ σ v = P.tameCharacter π σ ^ p • v) ∨
        (∀ σ ∈ P.inertiaSubgroupIn ℚ,
          (ρ.residual.baseChangeAlong ψk).ρ σ v = P.tameCharacter π σ ^ (p + 1) • v)) := by sorry
