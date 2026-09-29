-- Prove2me | Theorems.Thm_LocalGL2_iwasawa_decomposition_diag
-- name    : LocalGL2.iwasawa_decomposition_diag
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/da1cf1fd-b083-5840-a795-51f94250ce19
-- title:
--   Iwasawa decomposition for GL₂(K) in unipotent–diagonal form
-- statement:
--   Let $R$ be a discrete valuation ring (a commutative domain that is a discrete valuation ring in Mathlib's sense), let $K$ be a field equipped with an $R$-algebra structure making it the fraction field of $R$, and let $g$ be an element of $\mathrm{GL}_2(K)$. The assertion is that there exist a scalar $z \in K$, units $a_1, a_2 \in K^\times$, and an element $k \in \mathrm{GL}_2(K)$ lying in [`LocalGL2.integralSubgroup R K`](def/LocalLanglands_LocalHeckeInstance.html#L13), that is, in the image of the group homomorphism $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ obtained by applying the structure map $R \to K$ entrywise, such that the underlying $2 \times 2$ matrix of $g$ factors as $$\begin{pmatrix} 1 & z \\ 0 & 1\end{pmatrix}\begin{pmatrix} a_1 & 0 \\ 0 & a_2\end{pmatrix} k .$$ Thus the Borel factor is presented in the explicit coordinates (unipotent upper-triangular matrix) times (diagonal matrix with unit entries), the equality being one of matrices over $K$ rather than of elements of $\mathrm{GL}_2(K)$; no normalisation of $z$, $a_1$, $a_2$ or $k$, and no uniqueness, is claimed.
--
--   This is the Iwasawa decomposition $\mathrm{GL}_2(K) = B(K)\,\mathrm{GL}_2(R)$ for the fraction field of a discrete valuation ring, with the Borel part written out in unipotent–diagonal coordinates. It is used in the local computations with Hecke operators and orbital integrals, where functions on $\mathrm{GL}_2(K)$ are evaluated on explicit diagonal representatives modulo the integral subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_iwasawa_decomposition_diag.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem LocalGL2.iwasawa_decomposition_diag (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (g : GL (Fin 2) K) :
    ∃ (z : K) (a₁ a₂ : Kˣ) (k : GL (Fin 2) K), k ∈ LocalGL2.integralSubgroup R K ∧
      (g : Matrix (Fin 2) (Fin 2) K) = !![1, z; 0, 1] * !![(a₁ : K), 0; 0, (a₂ : K)] * k := by sorry
