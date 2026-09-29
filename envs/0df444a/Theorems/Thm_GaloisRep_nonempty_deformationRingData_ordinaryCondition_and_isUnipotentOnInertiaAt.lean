-- Prove2me | Theorems.Thm_GaloisRep_nonempty_deformationRingData_ordinaryCondition_and_isUnipotentOnInertiaAt
-- name    : GaloisRep.nonempty_deformationRingData_ordinaryCondition_and_isUnipotentOnInertiaAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/848b3dea-cb88-5d77-bf67-81de8bc70e0f
-- title:
--   Representability of the ordinary deformation problem with unipotent inertia at U
-- statement:
--   Let $\mathcal O$ be a discrete valuation domain which is adically complete for its maximal ideal and has finite residue field $k=\mathrm{ResidueField}\,\mathcal O$, and let $\bar\rho$ be a residual Galois representation over $k$, that is, a $k$-vector space $V$ with $\dim_k V=2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)=\mathrm{AlgebraicClosure}\,\mathbb Q\simeq_{\mathbb Q}\mathrm{AlgebraicClosure}\,\mathbb Q$ to $\mathrm{End}_k V$ factoring through a finite level. Let $p$ be a prime with $p\neq 2$ and let $S,U$ be finite sets of natural numbers. Assume: $\bar\rho$ is absolutely irreducible, in the sense that its base change to $\mathrm{AlgebraicClosure}\,k$ is irreducible; the rank-two adic representation [`GaloisRepAdic.ofResidualGaloisRep ρbar`](def/GaloisRep_Adic.html#L196) over the local ring $k$ satisfies `ordinaryCondition 𝒪 p S`, i.e. the predicates `DetIsCyclotomic p` and `IsOrdinaryAt p` hold and, for every prime $q\notin S$, every element of the inertia subgroup of every valuation subring of $\overline{\mathbb Q}$ lying over $q$ acts trivially; and, for every $q\in U$ which is prime and distinct from $p$, this same representation is unipotent on inertia at $q$, meaning that for every valuation subring of $\overline{\mathbb Q}$ lying over $q$ and every $\sigma$ in its inertia subgroup the characteristic polynomial of $\rho(\sigma)$ is $(X-1)^2$. Then [`GaloisRep.DeformationRingData 𝒪 ρbar 𝒟`](def/GaloisRep_DeformationRingData.html#L8) is nonempty for the condition $\mathcal D(\rho)$ given by `ordinaryCondition 𝒪 p S ρ` together with unipotence on inertia at every prime $q\in U$ with $q\neq p$: there exist a complete noetherian local $\mathcal O$-algebra $R$ whose structure map is local and for which the composite $\mathcal O\to R\to\mathrm{ResidueField}\,R$ is surjective, and a rank-two adic representation $\rho$ over $R$ of type $\mathcal D$ whose residual representation is equivalent to the base change of $\bar\rho$ along the induced map of residue fields, such that for every complete noetherian local $\mathcal O$-algebra $A$ with local structure map and surjective composite to its residue field, and every $\rho_A$ over $A$ of type $\mathcal D$ with residual representation equivalent to the corresponding base change of $\bar\rho$, there is a unique $\mathcal O$-algebra homomorphism $R\to A$ which is local and along which $\rho$ base-changes to a representation equivalent to $\rho_A$.
--
--   This is the representability statement for Mazur's deformation problem in the mixed form needed on the intermediate rungs of the level ladder: the ordinary condition of type $S$ with unipotent inertia imposed at an auxiliary finite set $U$ of primes. It is obtained from the general existence theorem for universal deformation rings together with the facts that the ordinary condition is a deformation condition and has finite-dimensional tangent space, and it is used in the construction of the patching data for the modularity lifting arguments at $p=3$ and in the level-lowering chain.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_nonempty_deformationRingData_ordinaryCondition_and_isUnipotentOnInertiaAt.lean

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem GaloisRep.nonempty_deformationRingData_ordinaryCondition_and_isUnipotentOnInertiaAt
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (S U : Finset ℕ)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hbar : GaloisRep.ordinaryCondition 𝒪 p S (GaloisRepAdic.ofResidualGaloisRep ρbar))
    (hbarU : ∀ q ∈ U, q.Prime → q ≠ p →
      (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q) :
    Nonempty (GaloisRep.DeformationRingData 𝒪 ρbar
      (fun _A _ _ _ ρ => GaloisRep.ordinaryCondition 𝒪 p S ρ ∧
        ∀ q ∈ U, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q)) := by sorry
