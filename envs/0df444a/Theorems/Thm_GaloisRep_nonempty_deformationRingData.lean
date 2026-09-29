-- Prove2me | Theorems.Thm_GaloisRep_nonempty_deformationRingData
-- name    : GaloisRep.nonempty_deformationRingData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/bda46e6f-14a7-56b7-8987-79b5f4a01d74
-- title:
--   Existence of a universal deformation ring of type D
-- statement:
--   Let $\mathcal{O}$ be a commutative ring that is a domain and a discrete valuation ring, complete for the adic topology of its maximal ideal, with finite residue field $k =$ `IsLocalRing.ResidueField 𝒪`. Let $\bar\rho$ be a residual Galois representation over $k$ in the project's sense ([`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22): a $k$-module $V$ with $\dim_k V = 2$ together with a monoid homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` to $\operatorname{End}_k V$ which factors through a finite level), and let $\mathcal{D}$ be a predicate, defined for every local $\mathcal{O}$-algebra $A$ carried by a type in `Type`, on the two-dimensional adically continuous representations [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16). Assume: (i) `habs`, $\bar\rho$ is absolutely irreducible, meaning its base change to `AlgebraicClosure k` is irreducible; (ii) `h𝒟`, $\mathcal{D}$ is a deformation condition in the project's sense, i.e. on Artinian test algebras ($\mathcal{O}\to A$ a local homomorphism inducing a surjection onto the residue field, $A$ Artinian) it is invariant under equivalence of representations, stable under base change along local $\mathcal{O}$-algebra maps, reflected by base change along injective such maps, and satisfied by a representation over $P$ as soon as it holds for the two pullbacks along the projections of a fibre-product diagram; and on complete Noetherian local $\mathcal{O}$-algebras $A$ with local structure map and surjective residue composite, $\mathcal{D}(\rho)$ holds if and only if it holds for every base change of $\rho$ along a surjection onto an Artinian test algebra; (iii) `hbar`, $\bar\rho$ itself, viewed via [`GaloisRepAdic.ofResidualGaloisRep`](def/GaloisRep_Adic.html#L196) as a representation over $k$, satisfies $\mathcal{D}$; (iv) `hfin`, tangent finiteness: the representations over the dual numbers $k[\varepsilon]$ which satisfy $\mathcal{D}$ and whose residual representation is equivalent to the base change of $\bar\rho$ form finitely many equivalence classes. The conclusion is that the type [`GaloisRep.DeformationRingData 𝒪 ρbar 𝒟`](def/GaloisRep_DeformationRingData.html#L8) is non-empty, i.e. there exist a ring $R$, commutative, local, Noetherian, complete for its maximal-ideal adic topology, an $\mathcal{O}$-algebra whose structure map is a local homomorphism and for which $\mathcal{O}\to R\to \operatorname{ResidueField} R$ is surjective, and a representation $\rho \in$ [`GaloisRepAdic R`](def/GaloisRep_Adic.html#L16) with $\mathcal{D}(\rho)$ whose residual representation is equivalent to the base change of $\bar\rho$ along the induced map of residue fields, such that for every commutative local Noetherian adically complete $\mathcal{O}$-algebra $A$ with local structure map and surjective residue composite, and every $\rho_A \in$ [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16) with $\mathcal{D}(\rho_A)$ whose residual representation is equivalent to the corresponding base change of $\bar\rho$, there is a unique $\mathcal{O}$-algebra homomorphism $\varphi : R \to A$ which is a local homomorphism and for which the base change of $\rho$ along $\varphi$ is equivalent to $\rho_A$. (The structure also records the hypothesis `habs` as a field.) Note that the universal property is stated for lifts up to equivalence of representations, not for framed lifts, and that uniqueness is uniqueness of $\varphi$ among $\mathcal{O}$-algebra maps with this property.
--
--   This is the representability theorem for deformation problems of Mazur's type, as in Mazur's original paper and in Theorem 2.36 of Darmon–Diamond–Taylor: an absolutely irreducible residual representation of type $\mathcal{D}$ with finite-dimensional type-$\mathcal{D}$ tangent space has a universal deformation ring. Compared with textbook statements, the hypotheses on $\mathcal{D}$ are exactly the project's `IsDeformationCondition` axioms (invariance, base change, reflection along injections, fibre products, and detection by Artinian quotients), the representations are the project's [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16)/[`ResidualGaloisRep`](def/GaloisRep_Residual.html#L22) data rather than matrix-valued continuous homomorphisms, and the conclusion is packaged as non-emptiness of the record `DeformationRingData`, which carries $R$, the universal representation and the universal property but does not assert minimality or a presentation of $R$. It is used to produce universal deformation rings for the flat, ordinary and strict-ordinary conditions combined with unipotence on inertia at auxiliary primes, and thence for the residual representations attached to $p$-torsion of semistable Weierstrass models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_nonempty_deformationRingData.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_GaloisRep_DeformationCondition

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.nonempty_deformationRingData
    (𝒪 : Type) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (habs : ρbar.IsAbsolutelyIrreducible)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (hbar : 𝒟 (GaloisRepAdic.ofResidualGaloisRep ρbar))
    (hfin : GaloisRep.TangentFinite 𝒪 ρbar 𝒟) :
    Nonempty (GaloisRep.DeformationRingData 𝒪 ρbar 𝒟) := by sorry
