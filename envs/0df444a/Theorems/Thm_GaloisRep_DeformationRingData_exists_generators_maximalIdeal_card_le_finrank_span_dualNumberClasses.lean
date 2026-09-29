-- Prove2me | Theorems.Thm_GaloisRep_DeformationRingData_exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses
-- name    : GaloisRep.DeformationRingData.exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/ab64a7a9-02cb-567a-8918-cb9569e6faaa
-- title:
--   Tangent space bound on generators of the deformation ring
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain, complete for its maximal-ideal adic topology, with finite residue field $k=\mathcal O/\mathfrak m_{\mathcal O}$, let $p$ be a prime with $p\neq 2$ and $p\in\mathfrak m_{\mathcal O}$, and let $\bar\rho$ be a residual Galois representation over $k$: a $2$-dimensional $k$-space $V$ with a monoid homomorphism $\bar\rho\colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{End}_k(V)$ factoring through a finite level. Assume $\bar\rho$, viewed as a representation over the local ring $k$, has cyclotomic determinant in the sense of `DetIsCyclotomic`: $p\in\mathfrak m_k$ and, for all $n$, $\sigma$ and $a$, if $\sigma$ raises every $p^n$-th root of unity to the $a$-th power then $\det\bar\rho(\sigma)-a$ lies in $(p^n)$. Let $\mathcal D$ be a predicate on $2$-dimensional adically continuous Galois representations over local $\mathcal O$-algebras, and let $D$ be a `DeformationRingData` for $\mathcal O$, $\bar\rho$ and $\mathcal D$: a complete noetherian local $\mathcal O$-algebra $R$ with $\mathcal O\to R$ local and $\mathcal O\to R\to R/\mathfrak m_R$ surjective, together with $\bar\rho$ absolutely irreducible and a representation $\rho$ over $R$ of type $\mathcal D$ whose residual representation is equivalent to the base change of $\bar\rho$, satisfying the universal property that every type-$\mathcal D$ representation with residual equivalent to $\bar\rho$ over such an algebra $A$ arises from a unique local $\mathcal O$-algebra map $R\to A$ up to equivalence; assume $\rho$ too has cyclotomic determinant for $p$. Give the dual numbers $k[\varepsilon]$ the $\mathcal O$-algebra structure coming from $\mathcal O\to k\to k[\varepsilon]$, and assume that for every $\mathcal O$-algebra homomorphism $\varphi\colon R\to k[\varepsilon]$ that is a local homomorphism the base change of $\rho$ along $\varphi$ satisfies $\mathcal D$. Then there are $m\in\mathbb N$ and $a_1,\dots,a_m\in\mathfrak m_R$ with $\mathfrak m_R\subseteq (a_1,\dots,a_m)+\mathfrak m_R^2+\mathfrak m_{\mathcal O}R$ and with $m$ at most the $k$-dimension of the $k$-span of the following subset of $H^1(\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q),\mathrm{ad}^0\bar\rho)$, where $\mathrm{ad}^0\bar\rho$ is the trace-zero part of the adjoint representation: the classes $x$ represented by some $1$-cocycle $c$ for which there exist a representation $\rho_A$ over $k[\varepsilon]$ of type $\mathcal D$ and a group homomorphism $\rho_d$ from the Galois group to the units of $\mathrm{End}_k(V)[\varepsilon]$ whose constant term is $\bar\rho$, such that $c(\sigma)=(\rho_d\sigma)_1\,\bar\rho(\sigma)^{-1}$ for all $\sigma$ and such that in suitable bases of $\rho_A$'s module over $k[\varepsilon]$ and of $V$ over $k$ the matrix of $\rho_A(\sigma)$ corresponds, under the identification of matrices over $k[\varepsilon]$ with dual numbers of matrices, to the pair of matrices of the two components of $\rho_d\sigma$.
--
--   This is the injectivity half of Mazur's identification of the reduced Zariski tangent space $\mathrm{Hom}_k(\mathfrak m_R/(\mathfrak m_R^2+\mathfrak m_{\mathcal O}R),k)$ of a universal deformation ring with the subspace of $H^1(\mathbb Q,\mathrm{ad}^0\bar\rho)$ cut out by the deformation condition: it bounds the number of generators of $\mathfrak m_R$ modulo $\mathfrak m_R^2+\mathfrak m_{\mathcal O}R$ by the dimension of the relevant Selmer-type group. It is used in the construction of Taylor–Wiles primes, where the deformation ring is presented as a quotient of a power series ring in a controlled number of variables.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_DeformationRingData_exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses.lean

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_AdZero
import Definitions.Def_GroupCohomology_TangentSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing groupCohomology TrivSqZeroExt

theorem GaloisRep.DeformationRingData.exists_generators_maximalIdeal_card_le_finrank_span_dualNumberClasses
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [Finite (ResidueField 𝒪)]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
    {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    (hdet : (GaloisRepAdic.ofResidualGaloisRep ρbar).DetIsCyclotomic p)
    {𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) (hdetR : D.ρ.DetIsCyclotomic p) :
    letI : Algebra 𝒪 (DualNumber (ResidueField 𝒪)) :=
      ((algebraMap (ResidueField 𝒪) (DualNumber (ResidueField 𝒪))).comp
        (algebraMap 𝒪 (ResidueField 𝒪))).toAlgebra
    (∀ (φ : D.R →ₐ[𝒪] DualNumber (ResidueField 𝒪))
        (hφ : IsLocalHom (φ : D.R →+* DualNumber (ResidueField 𝒪))),
        𝒟 (D.ρ.baseChangeAlong (φ : D.R →+* DualNumber (ResidueField 𝒪)) hφ)) →
    ∃ (m : ℕ) (a : Fin m → D.R), (∀ i, a i ∈ maximalIdeal D.R) ∧
      maximalIdeal D.R ≤ Ideal.span (Set.range a) ⊔ maximalIdeal D.R ^ 2 ⊔
        (maximalIdeal 𝒪).map (algebraMap 𝒪 D.R) ∧
      m ≤ Module.finrank (ResidueField 𝒪) (Submodule.span (ResidueField 𝒪)
        {x : H1 ρbar.adZero |
          ∃ c : cocycles₁ ρbar.adZero, H1π ρbar.adZero c = x ∧
          ∃ ρA : GaloisRepAdic (DualNumber (ResidueField 𝒪)),
            𝒟 ρA ∧
          ∃ ρd : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →*
              (DualNumber (Module.End (ResidueField 𝒪) ρbar.V))ˣ,
            IsDualLift ρbar.ρ.toHomUnits ρd ∧
            (∀ σ, ((c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →
                ↥(LinearMap.ker (LinearMap.trace (ResidueField 𝒪) ρbar.V))) σ :
                  Module.End (ResidueField 𝒪) ρbar.V) =
              dualLiftToCochain ρbar.ρ.toHomUnits ρd σ) ∧
            ∃ (b : Module.Basis (Fin 2) (DualNumber (ResidueField 𝒪)) ρA.V)
              (bbar : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V),
              ∀ σ, LinearMap.toMatrix b b (ρA.ρ σ) =
                Matrix.dualNumberEquiv.symm
                  ⟨LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).fst),
                    LinearMap.toMatrix bbar bbar
                      ((ρd σ : DualNumber (Module.End (ResidueField 𝒪) ρbar.V)).snd)⟩}) := by sorry
