-- Prove2me | Theorems.Thm_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq
-- name    : LocalGL2.exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/0927c218-ac14-5a9c-9dd3-d9ff2bfbd649
-- title:
--   Satake-type constant-term homomorphism for GL₂ over a discrete valuation ring
-- statement:
--   Let $R$ be a discrete valuation domain with fraction field $K$, let $\varpi \in R$ be irreducible with nonzero image in $K$, and assume the residue ring $R/(\varpi)$ is finite; let $R_0$ be a commutative ring. Write $G = \mathrm{GL}_2(K)$ and let $U =$ `integralSubgroup R K` be the image of $\mathrm{GL}_2(R)$ in $G$ under the map induced by $R \to K$. Set $t =$ `diagPi` $= \mathrm{diag}(\varpi,1)$ and $w \cdot t \cdot w =$ `localRepInf`, where $w$ is the image in $G$ of the Weyl matrix `weylR` over $R$. Assume the image of $U \cdot \{t \cdot (w t w)\}$ in $G/U$ is finite. Then there is an $R_0$-algebra homomorphism $S$ from the Hecke algebra `HeckeAlgebra (integralSubgroup R K) R₀` of the pair $(G,U)$ to the group algebra $R_0[\mathbb{Z} \times \mathbb{Z}]$ such that: (i) for every $f$ in the Hecke algebra and all $a,b \in \mathbb{Z}$, the coefficient of $S f$ at $(a,b)$ is the unordered sum over $c \in G/U$ of the indicator, evaluated at $c$, of the set of cosets admitting a representative $g$ with $g_{10} = 0$, $g_{00} = \varpi^a$, $g_{11} = \varpi^b$, applied to the function $c \mapsto f(\mathrm{out}(c))$ given by evaluating $f$ at a chosen representative; (ii) $S$ sends the indicator function of the double coset $U t U$ (with value $1$) to $\mathrm{Nat.card}(R/(\varpi)) \cdot e_{(1,0)} + e_{(0,1)}$; (iii) $S$ sends the indicator function of the double coset $U \cdot t(wtw) \cdot U$ to $e_{(1,1)}$.
--
--   This is the constant-term (Satake, or Iwasawa-decomposition) map on the spherical Hecke algebra of $\mathrm{GL}_2$ over a local field: integration of a bi-$\mathrm{GL}_2(R)$-invariant function along the upper unipotent subgroup, recorded here as an algebra homomorphism into $R_0[\mathbb{Z}^2]$ together with its values on the double cosets of $\mathrm{diag}(\varpi,1)$ and of the central-type element $\mathrm{diag}(\varpi,1) \cdot w\,\mathrm{diag}(\varpi,1)\,w$. It is used by [`AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime`](thm.html#AutomorphicForm.exists_heckeAlgHom_areMatchingLocal_of_inert_of_prime) to match local Hecke operators at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LocalGL2_exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq.lean

import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_LocalLanglands_HeckePair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise
open LocalGL2 HeckePair

theorem LocalGL2.exists_algHom_apply_eq_finsum_indicator_heckeIndicator_diagPi_eq
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (ϖ : R) (hϖ0 : algebraMap R K ϖ ≠ 0) (hϖ : Irreducible ϖ) [Finite (R ⧸ Ideal.span {ϖ})]
    {R₀ : Type*} [CommRing R₀]
    (hS : (QuotientGroup.mk '' ((integralSubgroup R K : Set (GL (Fin 2) K))
        * {diagPi ϖ hϖ0 * localRepInf ϖ hϖ0}) : Set (GL (Fin 2) K ⧸ integralSubgroup R K)).Finite) :
    ∃ S : HeckeAlgebra (integralSubgroup R K) R₀ →ₐ[R₀] AddMonoidAlgebra R₀ (ℤ × ℤ),
      (∀ (f : HeckeAlgebra (integralSubgroup R K) R₀) (a b : ℤ),
        (S f).coeff (a, b) = ∑ᶠ c : GL (Fin 2) K ⧸ integralSubgroup R K,
          Set.indicator
            {c : GL (Fin 2) K ⧸ integralSubgroup R K | ∃ g : GL (Fin 2) K, QuotientGroup.mk g = c ∧
              (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 ∧
              (g : Matrix (Fin 2) (Fin 2) K) 0 0 = algebraMap R K ϖ ^ a ∧
              (g : Matrix (Fin 2) (Fin 2) K) 1 1 = algebraMap R K ϖ ^ b}
            (fun c => (f : GL (Fin 2) K → R₀) (Quotient.out c)) c) ∧
      S (heckeIndicator R₀ (diagPi ϖ hϖ0) (finite_image_mul_diagPi ϖ hϖ0 hϖ)) =
        AddMonoidAlgebra.single (1, 0) (Nat.card (R ⧸ Ideal.span {ϖ}) : R₀) +
          AddMonoidAlgebra.single (0, 1) 1 ∧
      S (heckeIndicator R₀ (diagPi ϖ hϖ0 * localRepInf ϖ hϖ0) hS) = AddMonoidAlgebra.single (1, 1) 1 := by sorry
