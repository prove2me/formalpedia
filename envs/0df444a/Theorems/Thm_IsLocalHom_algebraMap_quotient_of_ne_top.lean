-- Prove2me | Theorems.Thm_IsLocalHom_algebraMap_quotient_of_ne_top
-- name    : IsLocalHom.algebraMap_quotient_of_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/ca3c0867-0333-50d4-b0cb-957aeab81d76
-- title:
--   Locality of the structure map passes to proper quotients
-- statement:
--   Let $\mathcal{O}$ and $A$ be commutative rings with $A$ local, and let $A$ be an $\mathcal{O}$-algebra whose structure map $\mathrm{algebraMap}\ \mathcal{O}\ A$ is a local homomorphism in the sense of Mathlib's `IsLocalHom`, that is, every $x \in \mathcal{O}$ whose image in $A$ is a unit is already a unit in $\mathcal{O}$. Let $I$ be an ideal of $A$ with $I \neq \top$, i.e. $I$ a proper ideal. The conclusion is that the induced structure map $\mathrm{algebraMap}\ \mathcal{O}\ (A \mathbin{⧸} I)$ of the quotient algebra is again a local homomorphism: any $x \in \mathcal{O}$ whose image in $A/I$ is a unit is a unit in $\mathcal{O}$. Here $A/I$ is a local ring automatically, being a nonzero quotient of the local ring $A$; no hypothesis beyond properness of $I$ is imposed, and $\mathcal{O}$ is not assumed local.
--
--   Routine bookkeeping about local homomorphisms of local algebras, needed because the test objects of a deformation problem are coefficient algebras presented as quotients $A/I$ (for instance $A/\mathfrak{m}^n$) and must come equipped with a local structure map. It is used in the verification that the flat, ordinary and strictly ordinary conditions are deformation conditions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalHom_algebraMap_quotient_of_ne_top.lean

import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocalHom.algebraMap_quotient_of_ne_top
    {𝒪 A : Type} [CommRing 𝒪] [CommRing A] [IsLocalRing A] [Algebra 𝒪 A]
    [IsLocalHom (algebraMap 𝒪 A)] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalHom (algebraMap 𝒪 (A ⧸ I)) := by sorry
