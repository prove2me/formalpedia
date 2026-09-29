-- Prove2me | Theorems.Thm_LocalGL2_existsUnique_algHom_heckeIndicator_eq
-- name    : LocalGL2.existsUnique_algHom_heckeIndicator_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/af81a6b6-d4fc-5f79-bf8f-a812311e3c08
-- title:
--   Algebra characters of the local Hecke algebra as Satake pairs
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$ (via an $R$-algebra structure on the field $K$ making it the fraction field), let $\varpi \in R$ be irreducible with nonzero image in $K$, and assume the quotient $R/(\varpi)$ is finite. Let $R_0$ be a commutative ring, let $A$ be a commutative $R_0$-algebra, let $a \in A$ and let $b \in A^{\times}$. Write $U =$ `integralSubgroup R K` for the image of $\mathrm{GL}_2(R)$ in $\mathrm{GL}_2(K)$ under the map induced by $R \to K$, and let `HeckeAlgebra` $U$ $R_0$ be the $R_0$-algebra of functions $\mathrm{GL}_2(K) \to R_0$ satisfying `IsHeckeFun`, i.e. invariant under left and right translation by $U$ and with support having finite image in $\mathrm{GL}_2(K)/U$. Put $\pi = \mathrm{diag}(\varpi,1)$ (`diagPi`) and $\mathrm{localRepInf} = w\,\pi\,w$, where $w$ is the image in $\mathrm{GL}_2(K)$ of the element `weylR` of $\mathrm{GL}_2(R)$. Assume the image of $U \cdot \{\pi \cdot \mathrm{localRepInf}\}$ in $\mathrm{GL}_2(K)/U$ is finite. Then there is exactly one $R_0$-algebra homomorphism $\chi$ from `HeckeAlgebra` $U$ $R_0$ to $A$ sending the indicator function of the double coset $U\pi U$ to $a$ and the indicator function of the double coset $U\,\pi\,\mathrm{localRepInf}\,U$ to the image of $b$ in $A$; the finiteness hypothesis needed for the first indicator is `finite_image_mul_diagPi`.
--
--   This is the purely algebraic form of the statement that characters of the spherical Hecke algebra of $\mathrm{GL}_2$ over a local ring correspond to Satake pairs: the values on the two generating double cosets $U\,\mathrm{diag}(\varpi,1)\,U$ and $U\,\mathrm{diag}(\varpi,1)\,w\,\mathrm{diag}(\varpi,1)\,w\,U$ may be prescribed arbitrarily in $A \times A^{\times}$, and determine the homomorphism. It is used in the construction of local Hecke characters matching a given system of eigenvalues, in [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime); no topology, continuity, or dictionary with unramified principal series is asserted.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_existsUnique_algHom_heckeIndicator_eq.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped Pointwise
open LocalGL2 HeckePair

theorem LocalGL2.existsUnique_algHom_heckeIndicator_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite)
    {A : Type*} [CommRing A] [Algebra R₀ A] (a : A) (b : Aˣ) :
    ∃! χ : HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] A,
      χ (heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) = a ∧
      χ (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS) = (b : A) := by sorry
