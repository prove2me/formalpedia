-- Prove2me | Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers
-- name    : IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/22da0ac6-392d-5bbd-aed5-80a220f99f7f
-- title:
--   Finite adeles decompose as K + widehatA
-- statement:
--   Let $A$ be a Dedekind domain, $K$ a field equipped with an $A$-algebra structure making it the fraction field of $A$, and write $\mathrm{HeightOneSpectrum}\,A$ for the set of nonzero prime ideals $v$ of $A$, each giving a completion $K_v =$ `v.adicCompletion K` of $K$ with valuation ring $\mathcal{O}_v =$ `v.adicCompletionIntegers K`. The assertion is that for every element $a$ of the finite adele ring of $A$ with respect to $K$ — the restricted product of the $K_v$ with respect to the $\mathcal{O}_v$ — there exists a single global element $x \in K$ such that for every nonzero prime $v$ the difference $a_v - x$, the $v$-component of $a$ minus the image of $x$ under the canonical map $K \to K_v$, lies in $\mathcal{O}_v$. Thus the additive decomposition $\mathbb{A}_K^f = K + \prod_v \mathcal{O}_v$ holds, with the integral part taken over all finite places simultaneously; no hypothesis on the class group or on $A$ beyond being a Dedekind domain is imposed.
--
--   This is the additive form of strong approximation at the finite places: the diagonal image of $K$ together with the integral adeles exhausts $\mathbb{A}_K^f$; no archimedean place occurs, and the variant in which one place is excluded is a different statement. It is used in the adelic parts of the development, for instance in identifying elements of $K$ inside the adeles by local conditions and in the lattice and order computations for quaternion algebras over $\mathbb{Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain

theorem IsDedekindDomain.FiniteAdeleRing.exists_forall_sub_algebraMap_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by sorry
