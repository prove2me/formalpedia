-- Prove2me | Theorems.Thm_GaloisRep_nonempty_deformationRingData_flatCondition_and_isUnipotentOnInertiaAt
-- name    : GaloisRep.nonempty_deformationRingData_flatCondition_and_isUnipotentOnInertiaAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/fec41b23-00ab-51ca-84d8-bc1904d55ed6
-- title:
--   Universal deformation ring: flat of type S, unipotent inertia on U
-- statement:
--   Let $\mathcal{O}$ be a discrete valuation ring which is a domain, complete for the adic topology of its maximal ideal, with finite residue field $k = \mathrm{ResidueField}\,\mathcal{O}$, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{End}_k(V)$ that is trivial on the subgroup fixing some finite extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. Let $p$ be a prime with $p \neq 2$ whose image in $\mathcal{O}$ lies in the maximal ideal, and let $S, U$ be finite sets of naturals. Assume $\bar\rho$ is absolutely irreducible, i.e. its base change to $\overline{k}$ is irreducible; assume that $\bar\rho$, regarded as an adic representation over the field $k$ via [`GaloisRepAdic.ofResidualGaloisRep`](def/GaloisRep_Adic.html#L196), satisfies [`GaloisRep.flatCondition 𝒪 p S`](def/GaloisRep_Flat.html#L47), namely the predicates `DetIsCyclotomic p` and `IsFlatAt p` hold for it and it is unramified at every prime $q \notin S$ (for each valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $P$, the inertia subgroup of $P$ over $\mathbb{Q}$ acts trivially); and assume that for every prime $q \in U$ with $q \neq p$ it is unipotent on inertia at $q$, i.e. every element of such an inertia subgroup acts with characteristic polynomial $(X-1)^2$. The conclusion is that the type [`GaloisRep.DeformationRingData`](def/GaloisRep_DeformationRingData.html#L8) for $\bar\rho$ and the deformation condition $\mathcal{D}(\rho) =$ (`flatCondition 𝒪 p S` for $\rho$, together with unipotence on inertia at each prime $q \in U$, $q \neq p$) is nonempty: there exist a noetherian local $\mathcal{O}$-algebra $R$, complete for its maximal-adic topology, with local structure map and with $\mathcal{O} \to R \to \mathrm{ResidueField}\,R$ surjective, and a rank-two adic representation $\rho$ over $R$ satisfying $\mathcal{D}$ whose residual representation is equivalent to the base change of $\bar\rho$ along the induced map of residue fields, such that for every complete noetherian local $\mathcal{O}$-algebra $A$ of the same kind and every adic representation $\rho_A$ over $A$ satisfying $\mathcal{D}$ with residual representation equivalent to the corresponding base change of $\bar\rho$, there is a unique $\mathcal{O}$-algebra map $\varphi\colon R \to A$ which is local and for which the base change of $\rho$ along $\varphi$ is equivalent to $\rho_A$.
--
--   This is the representability statement of Mazur's deformation theory, in the form refined by Ramakrishna to allow the flat condition at $p$, for the deformation problem that imposes flatness and determinant conditions of type $S$ at $p$ together with unipotent inertia at an auxiliary finite set $U$ of primes. It provides the universal deformation rings used on the Hecke-algebra side of the patching argument, and is cited in the construction of patching data and in the comparison of a Hecke algebra with a deformation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_nonempty_deformationRingData_flatCondition_and_isUnipotentOnInertiaAt.lean

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem GaloisRep.nonempty_deformationRingData_flatCondition_and_isUnipotentOnInertiaAt
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪) (S U : Finset ℕ)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (hbar : GaloisRep.flatCondition 𝒪 p S (GaloisRepAdic.ofResidualGaloisRep ρbar))
    (hbarU : ∀ q ∈ U, q.Prime → q ≠ p →
      (GaloisRepAdic.ofResidualGaloisRep ρbar).IsUnipotentOnInertiaAt q) :
    Nonempty (GaloisRep.DeformationRingData 𝒪 ρbar
      (fun _A _ _ _ ρ => GaloisRep.flatCondition 𝒪 p S ρ ∧
        ∀ q ∈ U, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q)) := by sorry
