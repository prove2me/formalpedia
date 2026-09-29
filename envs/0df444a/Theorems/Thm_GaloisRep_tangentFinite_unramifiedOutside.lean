-- Prove2me | Theorems.Thm_GaloisRep_tangentFinite_unramifiedOutside
-- name    : GaloisRep.tangentFinite_unramifiedOutside
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/5366c6b5-572c-5339-b62f-c6c3d5dcfc6e
-- title:
--   Tangent finiteness for deformations unramified outside S
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring whose residue field $k = \mathrm{ResidueField}\,\mathcal{O}$ is finite, let $\bar\rho$ be a residual representation over $k$ — that is, a $k$-vector space $V$ with $\dim_k V = 2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ (the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`) to $\mathrm{End}_k V$ that kills the fixing subgroup of some finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ — and let $S$ be a finite set of natural numbers. Consider the deformation condition which, for any local $\mathcal{O}$-algebra $A$, holds of a two-dimensional free adically continuous $A$-representation $\rho$ of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ exactly when for every prime $q \notin S$, every valuation subring $P$ of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $P$ and every $\sigma$ in the image in $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup of $P$, one has $\rho(\sigma) = 1$; the condition does not otherwise refer to $A$. The assertion is `TangentFinite` for this condition: the set of representations $\rho$ over the dual numbers $k[\varepsilon]$ which satisfy the condition and whose reduction (base change along $k[\varepsilon] \to \mathrm{ResidueField}(k[\varepsilon])$) is isomorphic to the corresponding base change of $\bar\rho$, taken up to $k[\varepsilon]$-linear Galois-equivariant isomorphism, is finite. No irreducibility or other hypothesis on $\bar\rho$ is imposed.
--
--   This is Mazur's finiteness condition on the tangent space for a deformation problem with ramification bounded outside a finite set of primes, one of the hypotheses needed for representability of the deformation functor. It serves as the basic input from which the corresponding tangent-finiteness statements for the ordinary and flat conditions, [`GaloisRep.tangentFinite_ordinaryCondition`](thm.html#GaloisRep.tangentFinite_ordinaryCondition) and [`GaloisRep.tangentFinite_flatCondition`](thm.html#GaloisRep.tangentFinite_flatCondition), are deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_tangentFinite_unramifiedOutside.lean

import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing

theorem GaloisRep.tangentFinite_unramifiedOutside (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    [Finite (ResidueField 𝒪)] (ρbar : ResidualGaloisRep (ResidueField 𝒪)) (S : Finset ℕ) :
    TangentFinite 𝒪 ρbar (fun _A _ _ _ ρ => ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q) := by sorry
