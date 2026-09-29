-- Prove2me | Theorems.Thm_LocalGL2_finite_image_integralSubgroup_mul_singleton
-- name    : LocalGL2.finite_image_integralSubgroup_mul_singleton
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/341a7b8f-4b29-5754-a744-23eb7ef1b435
-- title:
--   Finiteness of the coset image of GL₂(R)g
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure exhibiting it as a fraction field of $R$. Let $\varpi \in R$ be an irreducible element and assume the quotient ring $R/(\varpi)$ is finite; thus $R$ has finite residue field, although $\varpi$ itself does not appear in the conclusion. Write $U =$ `integralSubgroup R K` for the subgroup of $\mathrm{GL}_2(K)$ defined as the range of the homomorphism $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ induced by $\mathrm{algebraMap}\ R\ K$ entrywise, i.e. the image of $\mathrm{GL}_2(R)$ in $\mathrm{GL}_2(K)$. Then for every $g \in \mathrm{GL}_2(K)$, the image of the pointwise product set $U \cdot \{g\} = Ug$ under the canonical map $\mathrm{GL}_2(K) \to \mathrm{GL}_2(K)/U$ onto the set of cosets $xU$ is a finite subset of $\mathrm{GL}_2(K)/U$. Equivalently: the single coset $Ug$ meets only finitely many cosets $xU$. The assertion is made for one element $g$ at a time, not for a double coset $UgU$ as a whole.
--
--   This is the local finiteness statement underlying the definition of Hecke operators for $\mathrm{GL}_2$ over a local field with finite residue field: it says that $\mathrm{GL}_2(R)$ is a Hecke-compatible (almost normal) subgroup of $\mathrm{GL}_2(K)$, so that double-coset indicator functions have finite support in the coset space. It is used to discharge the finiteness hypothesis in the construction of the abstract Hecke algebra action on automorphic forms, and is cited by the results on Hecke word sums, cut traces and matching local Hecke operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_finite_image_integralSubgroup_mul_singleton.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise
open LocalGL2

theorem LocalGL2.finite_image_integralSubgroup_mul_singleton
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})] (g : GL (Fin 2) K) :
    (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K)) * {g}) :
      Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite := by sorry
