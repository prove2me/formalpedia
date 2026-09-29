-- Prove2me | Theorems.Thm_ModularCurve_isRoot_map_Phi_apply_jBar
-- name    : ModularCurve.isRoot_map_Phi_apply_jBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/c96bc010-956f-5495-8cce-b337ce9af311
-- title:
--   Any algebra image of j(q^N) is a root of Φ
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure and let $N$ be a nonzero natural number. Let `data` be a modular polynomial datum of level $N$: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic (in $Y$), whose degree equals `dedekindPsi N` $= \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies $\Phi = 0$ after its coefficient polynomials are evaluated at the Laurent series $jq = q^{-1}\cdot(\text{power series } jNumQ)$ over $\mathbb{Q}$ and the outer variable at `jqN N`. Let $A$ be a commutative $L$-algebra and let $\varphi$ be an $L$-algebra homomorphism from `laurentBaseChange L (modularFunctionFieldFull N)` to $A$; here `modularFunctionFieldFull N` is the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the series `qExpand ℚ d jq` for the divisors $d$ of $N$ (substitution of $q^d$ for $q$, realised as the ring homomorphism rescaling exponents by $d$), and `laurentBaseChange` is the subfield of $L((q))$ generated over $L$ by the coefficientwise images of that set under $\mathbb{Q} \to L$. Then, writing $x = \varphi(jq)$ and $y = \varphi(\mathrm{qExpand}\,\mathbb{Q}\,N\,jq)$ for the images of these two distinguished elements, the polynomial in $A[Y]$ obtained from $\Phi$ by applying $\mathbb{Z} \to A$ to its integer coefficients and substituting $x$ for $X$ has $y$ as a root.
--
--   This is the modular equation for level $N$ transported along an arbitrary algebra map out of the base-changed modular function field: classically, over a point of the $j$-line the function $j(N\tau)$ takes a value which is a root of $\Phi_N(j, \cdot)$. It is used in the analysis of places of the level-$N$ modular function field and of their reductions, in particular for the divisibility of the order of $j$ at such a place and for the description of cusp charts in the characteristic-$p$ fibre model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isRoot_map_Phi_apply_jBar.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.isRoot_map_Phi_apply_jBar (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N]
    (data : ModularPolynomialData N) (A : Type*) [CommRing A] [Algebra L A]
    (φ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L] A) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A)
      (φ ⟨coeffEmb L jq, coeffEmb_mem_laurentBaseChange L (jq_mem_full N)⟩))).IsRoot
      (φ ⟨coeffEmb L (qExpand ℚ N jq),
        coeffEmb_mem_laurentBaseChange L (jqd_mem_full N (dvd_refl N))⟩) := by sorry
