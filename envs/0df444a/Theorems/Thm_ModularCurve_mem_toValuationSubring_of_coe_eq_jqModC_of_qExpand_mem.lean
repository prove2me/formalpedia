-- Prove2me | Theorems.Thm_ModularCurve_mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem
-- name    : ModularCurve.mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/11aa811a-208d-5148-a7d2-225c8442bf9d
-- title:
--   Integrality of j(q) over ℤ[j(q^ℓ)] at a place
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $\ell$ be a natural number which is nonzero. Let $F$ be an intermediate field of the field of formal Laurent series $L((q))$ over $L$, and let $P$ be a place of $F$ over $L$ in the project's sense, i.e. a valuation subring of $F$ that contains the image of $L$ under the structure map, is not the whole of $F$, and is a principal ideal ring. Let $x, y \in F$ be two elements such that, as Laurent series, $x$ equals [`ModularCurve.jqModC L`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the image in $L[[q]]$ of the integral power series $\mathrm{jNum} = E_4^3 \cdot \eta^{-24}$-type numerator (the $q$-expansion of the modular invariant $j$), and $y$ equals the image of that same Laurent series under [`ModularCurve.qExpand L ℓ`](def/ModularCurve_X0.html#L25), the ring homomorphism of Laurent series obtained by embedding the exponent domain along multiplication by $\ell$ on $\mathbb{Z}$, i.e. the substitution $q \mapsto q^{\ell}$; so $y$ is the $q$-expansion of $j(q^{\ell})$. The assertion is: if $y$ lies in the valuation subring attached to $P$, then so does $x$.
--
--   This is the classical statement that $j(q)$ is integral over $\mathbb{Z}[j(q^{\ell})]$, read at a place of a field of $q$-expansions: a place at which $j(q^{\ell})$ is regular is also a place at which $j(q)$ is regular. It is used in the analysis of Hecke correspondences on the modular curves $X_1(p)$, in the lemmas computing Hecke divisors and reductions on two-chart models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.mem_toValuationSubring_of_coe_eq_jqModC_of_qExpand_mem
    (L : Type*) [Field L] [Algebra ℚ L] (ℓ : ℕ) [NeZero ℓ]
    (F : IntermediateField L (LaurentSeries L)) (P : AlgebraicCurve.Place L F) (x y : F)
    (hx : (x : LaurentSeries L) = ModularCurve.jqModC L)
    (hy : (y : LaurentSeries L) = ModularCurve.qExpand L ℓ (ModularCurve.jqModC L))
    (hyP : y ∈ P.toValuationSubring) : x ∈ P.toValuationSubring := by sorry
