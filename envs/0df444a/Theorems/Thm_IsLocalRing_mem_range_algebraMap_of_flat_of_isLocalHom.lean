-- Prove2me | Theorems.Thm_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom
-- name    : IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/e8f22a69-dcdc-5f10-b963-ac86e52d75ec
-- title:
--   S ∩ K = R for a flat local homomorphism of local domains
-- statement:
--   Let $R$ and $S$ be commutative local integral domains and let $f \colon R \to S$ be a ring homomorphism which is flat (as a ring homomorphism, i.e. $S$ is flat as an $R$-module via $f$) and local, in the sense that it carries the maximal ideal of $R$ into that of $S$. Let $K$ and $L$ be fields with $K$ a fraction field of $R$ and $L$ a fraction field of $S$, and suppose $L$ is moreover an algebra over $K$ and over $R$ in such a way that $R \to K \to L$ is a tower of scalars, and that the two routes from $R$ into $L$ agree with $f$: for every $r \in R$, the image of $r$ under $R \to L$ equals the image of $f(r)$ under $S \to L$. Then, for $x \in K$, if the image of $x$ in $L$ lies in the image of the structure map $S \to L$, then $x$ lies in the image of the structure map $R \to K$. In other words, inside $L$ one has $S \cap K = R$.
--
--   This is the standard descent statement that a flat local homomorphism of local domains is "pure" in the sense that elements of the smaller fraction field which become regular upstairs are already regular downstairs. Geometrically it says that for a flat local homomorphism of local rings of integral schemes, a rational function on the target regular at the image point is regular at the source point; it is used in the analysis of semistable models, where it feeds into the comparison of local rings after base change to a finite level and into the criteria [`AlgebraicCurve.SemistableModel.mem_localRing_iff_mem_range_of_level`](thm.html#AlgebraicCurve.SemistableModel.mem_localRing_iff_mem_range_of_level) and [`AlgebraicCurve.mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed`](thm.html#AlgebraicCurve.mem_localRing_of_forall_specializes_mem_localRing_of_ringEquiv_adicCompletion_stalk_of_isIntegrallyClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_mem_range_algebraMap_of_flat_of_isLocalHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v u' v'

theorem IsLocalRing.mem_range_algebraMap_of_flat_of_isLocalHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsDomain R] [IsDomain S]
    (f : R →+* S) (hf : f.Flat) [IsLocalHom f]
    (K : Type u') (L : Type v') [Field K] [Field L] [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [IsFractionRing S L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    (hcomm : ∀ r : R, algebraMap R L r = algebraMap S L (f r))
    (x : K) (hx : algebraMap K L x ∈ (algebraMap S L).range) :
    x ∈ (algebraMap R K).range := by sorry
