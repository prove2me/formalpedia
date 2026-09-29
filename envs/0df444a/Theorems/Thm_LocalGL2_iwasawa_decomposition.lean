-- Prove2me | Theorems.Thm_LocalGL2_iwasawa_decomposition
-- name    : LocalGL2.iwasawa_decomposition
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/f74bc7a4-0bfb-517f-b0c2-b99b7666f85e
-- title:
--   Iwasawa decomposition for GL₂ over a fraction field of a DVR
-- statement:
--   Let $R$ be a commutative domain which is a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure exhibiting $K$ as a fraction field of $R$, so that the structure map $R \to K$ is the inclusion of $R$ into its field of fractions. Let $g$ be an element of the general linear group $\mathrm{GL}(\mathrm{Fin}\ 2, K)$ of invertible $2\times 2$ matrices over $K$. The assertion is that there exist $b, k \in \mathrm{GL}(\mathrm{Fin}\ 2, K)$ such that: $k$ lies in [`LocalGL2.integralSubgroup R K`](def/LocalLanglands_LocalHeckeInstance.html#L13), that is, in the image of the group homomorphism $\mathrm{GL}(\mathrm{Fin}\ 2, R) \to \mathrm{GL}(\mathrm{Fin}\ 2, K)$ obtained by applying the structure map $R \to K$ to the matrix entries; the underlying matrix of $b$ has vanishing entry in position $(1,0)$, i.e. $b$ is upper triangular; and $g = b \cdot k$ in $\mathrm{GL}(\mathrm{Fin}\ 2, K)$. No condition is imposed on $b$ beyond the vanishing of its lower-left entry, and the factorisation is not claimed to be unique.
--
--   This is the non-archimedean Iwasawa decomposition $\mathrm{GL}_2(K) = B \cdot \mathrm{GL}_2(R)$ for the Borel subgroup $B$ of upper-triangular matrices and the integral maximal compact $\mathrm{GL}_2(R)$. It is the basic structural input for the local Hecke-algebra and orbital-integral computations in this development, and is used, for instance, in the evaluation of weighted orbital integrals of indicator functions at diagonal elements and in the existence of Borel factorisations of adelic matrices.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_iwasawa_decomposition.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalGL2.iwasawa_decomposition (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (g : GL (Fin 2) K) :
    ∃ b k : GL (Fin 2) K, k ∈ LocalGL2.integralSubgroup R K ∧
      (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧ g = b * k := by sorry
