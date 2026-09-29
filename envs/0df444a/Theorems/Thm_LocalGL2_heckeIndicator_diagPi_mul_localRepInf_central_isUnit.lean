-- Prove2me | Theorems.Thm_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_central_isUnit
-- name    : LocalGL2.heckeIndicator_diagPi_mul_localRepInf_central_isUnit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/69f661d7-2e58-54f2-a9b1-1328b7aa37a2
-- title:
--   Scalar double-coset indicator is a central unit
-- statement:
--   Let $R$ be a commutative ring, $K$ a field and $R \to K$ an algebra map, let $\varpi \in R$ be an element whose image $\operatorname{algebraMap} R K\,\varpi$ in $K$ is nonzero, and let $R_0$ be a commutative ring of coefficients. Write $U =$ `integralSubgroup R K` for the image of $\mathrm{GL}_2(R)$ in $G = \mathrm{GL}_2(K)$ under the entrywise algebra map, $g_1 =$ `diagPi ϖ hϖ0` for the invertible matrix $\mathrm{diag}(\varpi,1)$ over $K$ (with inverse $\mathrm{diag}(\varpi^{-1},1)$), and $g_2 =$ `localRepInf ϖ hϖ0` $= w\,g_1\,w$, where $w =$ `weylInt R K` is the image in $G$ of the matrix `weylR` over $R$. Assume `hfin`: the image of $U \cdot \{g_1 g_2\}$ in the coset space $G / U$ is finite. Then the element `heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin` of the Hecke algebra `HeckeAlgebra U R₀` — the function $G \to R_0$ taking the value $1$ on the double coset $U\,g_1g_2\,U$ and $0$ elsewhere, which is bi-$U$-invariant with finitely many cosets in its support — both commutes with every element $f$ of `HeckeAlgebra U R₀` under the convolution product and is a unit of that ring. No hypothesis on $R$ beyond commutativity is imposed; in particular $R$ need not be a discrete valuation ring and $\varpi$ need not be a uniformiser.
--
--   The element $g_1g_2$ is the central scalar matrix with entries the image of $\varpi$, up to sign, so its double coset is a single coset and the corresponding indicator plays the role of the invertible (Laurent) variable in the structure theory of the spherical Hecke algebra of the pair $(\mathrm{GL}_2(K), \mathrm{GL}_2(R))$. It is used in the construction of the Hecke algebra homomorphism in [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_heckeIndicator_diagPi_mul_localRepInf_central_isUnit.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise
open LocalGL2 HeckePair

theorem LocalGL2.heckeIndicator_diagPi_mul_localRepInf_central_isUnit
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0)
    {R₀ : Type*} [CommRing R₀]
    (hfin : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    (∀ f : HeckeAlgebra (integralSubgroup R K) R₀,
        heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin * f
          = f * heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin) ∧
      IsUnit (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hfin :
        HeckeAlgebra (integralSubgroup R K) R₀) := by sorry
