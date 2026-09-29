-- Prove2me | Theorems.Thm_GaloisRep_isDeformationCondition_strictOrdinaryCondition
-- name    : GaloisRep.isDeformationCondition_strictOrdinaryCondition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/4516f4e1-cbc4-5690-857a-7a960a1eb1d2
-- title:
--   Strict ordinary condition is a deformation condition, p odd
-- statement:
--   Fix a commutative coefficient ring $\mathcal{O}$, a prime $p$ with $p \neq 2$, and a finite set $S$ of natural numbers. The predicate [`GaloisRep.strictOrdinaryCondition`](def/GaloisRep_StrictOrdinary.html#L28) $\mathcal{O}\,p\,S$ assigns to a local ring $A$ and a two-dimensional adic Galois representation $\rho$ over $A$ (a finite free $A$-module $V$ with $\operatorname{finrank}_A V = 2$ together with a multiplicative action of $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ satisfying the adic continuity condition) the conjunction of: (i) $p \in \mathfrak{m}_A$ and, for all $n$, all $\sigma$ and all $a$ such that $\sigma$ acts on $p^n$-th roots of unity by $\mu \mapsto \mu^a$, $\det \rho(\sigma) - a \in (p^n)$; (ii) $p \in \mathfrak{m}_A$ and, for every valuation subring $P$ of $\overline{\mathbb{Q}}$ lying over $p$, existence of a line $L = A\cdot b_0$ spanned by a member of an $A$-basis of $V$ which is stable under the decomposition subgroup of $P$, on which the inertia subgroup acts trivially modulo $L$ (i.e. $\rho(\sigma)v - v \in L$ for $\sigma$ inertial), and such that each decomposition-group element $\sigma$ acts by a scalar $x$ on $L$ and by a scalar $z$ on $V/L$ with $x - a z \in (p^n)$ whenever $\sigma$ acts as $\mu \mapsto \mu^a$ on $p^n$-th roots of unity; (iii) $\rho$ is unramified at every prime $q \notin S$, in the sense that $\rho(\sigma) = 1$ for all $\sigma$ in the inertia subgroup of any valuation subring lying over $q$. The theorem asserts that this predicate is a deformation condition in the sense of [`GaloisRep.IsDeformationCondition`](def/GaloisRep_DeformationCondition.html#L19): it is invariant under isomorphism of representations over Artinian test algebras (local $\mathcal{O}$-algebras that are Artinian, with local structural map and surjective induced map to the residue field); it is preserved by base change along local $\mathcal{O}$-algebra maps between test algebras; it descends along injective such maps; it descends along a fibre-product datum, that is, from the two projections of a test algebra $P$ mapping jointly injectively to test algebras $A$, $B$ over a common $C$ with the surjectivity-onto-the-fibre-product property; and, for Noetherian $\mathfrak{m}$-adically complete $\mathcal{O}$-algebras $A$ with local structural map and surjective induced residue map, it holds for $\rho$ if and only if it holds for every base change of $\rho$ along a surjective local $\mathcal{O}$-algebra map onto an Artinian test algebra.
--
--   This is the verification of Mazur's axioms for Wiles's strict ordinary condition of type $S$, so that the associated deformation functor fits into the general representability and tangent-space framework for deformation rings. It is used in the construction of the strict ordinary universal deformation ring, and is cited by the corresponding statement for the strict ordinary condition combined with unipotence on inertia.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_isDeformationCondition_strictOrdinaryCondition.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_StrictOrdinary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.isDeformationCondition_strictOrdinaryCondition (𝒪 : Type) [CommRing 𝒪]
    {p : ℕ} {S : Finset ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    GaloisRep.IsDeformationCondition 𝒪 (GaloisRep.strictOrdinaryCondition 𝒪 p S) := by sorry
