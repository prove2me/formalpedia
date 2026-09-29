-- Prove2me | Theorems.Thm_IsLocalRing_isLocalProartinianAlgebra_adicTopology
-- name    : IsLocalRing.isLocalProartinianAlgebra_adicTopology
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/77ee8939-50c2-5b31-920a-2e266f8ca70c
-- title:
--   Complete noetherian local algebras are pro-Artinian for the adic topology
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring whose residue field is finite, and let $R$ be a commutative local ring that is noetherian and complete for its maximal-ideal-adic filtration (in the sense of `IsAdicComplete (maximalIdeal R) R`), equipped with an $\mathcal{O}$-algebra structure whose structure map $\mathcal{O} \to R$ is local. Assume furthermore that the composite of $\mathcal{O} \to R$ with the residue map $R \to R/\mathfrak{m}_R$ is surjective, i.e. $R$ has the same residue field as $\mathcal{O}$. Then, when $R$ carries the $\mathfrak{m}_R$-adic topology, $R$ is a local pro-Artinian $\mathcal{O}$-algebra in the sense of `IsLocalProartinianAlgebra`: $R$ is a topological ring and a local ring; its topology is linear over $R$ (it admits a neighbourhood basis of $0$ consisting of ideals), it is $T_0$, and $R$ is complete for the associated right uniformity, while for every ideal $I \subseteq R$ that is open the quotient $R/I$ is an Artinian ring; the structure map $\mathcal{O} \to R$ is local; and $\mathcal{O} \to R/\mathfrak{m}_R$ is surjective.
--
--   This identifies the objects of the classical deformation-theoretic category of complete noetherian local rings with fixed finite residue field (Mazur, Schlessinger) with the topological notion of local pro-Artinian algebra used in the formalised deformation theory, so that results about the latter apply to every complete noetherian local algebra arising in the argument. It is used in the construction of Hecke–Galois representation data attached to points of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isLocalProartinianAlgebra_adicTopology.lean

import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
open IsLocalRing Deformation

theorem IsLocalRing.isLocalProartinianAlgebra_adicTopology
    {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    [Algebra 𝒪 R] [IsLocalHom (algebraMap 𝒪 R)]
    (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap 𝒪 R))) :
    letI : TopologicalSpace R := (maximalIdeal R).adicTopology
    IsLocalProartinianAlgebra 𝒪 R := by sorry
