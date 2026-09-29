-- Prove2me | Theorems.Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi
-- name    : HeckeIntegralSeam.exists_isHeckeCosetSystem_integralSubgroup_diagPi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/aa956ab3-acf2-5ae0-8457-ef0a30de4ebe
-- title:
--   Existence of a finite Hecke coset system for diag(varpi,1)
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, and let $K$ be a field equipped with an $R$-algebra structure exhibiting it as the fraction field of $R$. Let $\varpi \in R$ be irreducible, assume the residue ring $R/(\varpi)$ is finite, and assume $\varpi$ has nonzero image in $K$. The assertion is that there exist a natural number $n$ and a family $rT : \mathrm{Fin}\ n \to \mathrm{GL}_2(K)$ satisfying [`HeckeIntegralSeam.IsHeckeCosetSystem`](def/LocalLanglands_HeckeCosetSystem.html#L15) for the subgroup $U =$ [`LocalGL2.integralSubgroup R K`](def/LocalLanglands_LocalHeckeInstance.html#L13), the range of the entrywise map $\mathrm{GL}_2(R) \to \mathrm{GL}_2(K)$ induced by $R \to K$, and the element $g =$ [`LocalGL2.diagPi`](def/LocalLanglands_HeckeCosetLocal.html#L68), the unit of $\mathrm{GL}_2(K)$ given by the matrix $\mathrm{diag}(\varpi, 1)$ together with the inverse $\mathrm{diag}(\varpi^{-1}, 1)$. Unfolding that structure, the three conclusions are: each $rT\,i$ lies in the double coset, i.e. in the set product $U \cdot \{g\} \cdot U$; every element $x$ of that double coset satisfies $xU = (rT\,i)U$ in the quotient $\mathrm{GL}_2(K)/U$ for some index $i$; and the map sending $i$ to the class of $rT\,i$ in $\mathrm{GL}_2(K)/U$ is injective. Thus the double coset is covered by the $n$ pairwise distinct left cosets $(rT\,i)U$, with representatives drawn from the double coset itself.
--
--   This is the coset decomposition underlying the local Hecke operator at $\varpi$: classically the double coset $\mathrm{GL}_2(R)\,\mathrm{diag}(\varpi,1)\,\mathrm{GL}_2(R)$ breaks into $|R/\varpi| + 1$ left cosets, indexed by $\mathbb{P}^1(R/\varpi)$. It supplies the coset-system hypothesis required by the automorphic-form statements on Hecke-word sums and on limits of integrals over hyperbolic and unipotent cells.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeIntegralSeam_exists_isHeckeCosetSystem_integralSubgroup_diagPi.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckeCosetSystem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise
open LocalGL2

theorem HeckeIntegralSeam.exists_isHeckeCosetSystem_integralSubgroup_diagPi
    {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    (hϖ0 : algebraMap R K ϖ ≠ 0) :
    ∃ (n : ℕ) (rT : Fin n → GL (Fin 2) K),
      HeckeIntegralSeam.IsHeckeCosetSystem (LocalGL2.integralSubgroup R K) (LocalGL2.diagPi ϖ hϖ0) rT := by sorry
