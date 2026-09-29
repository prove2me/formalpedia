-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul
-- name    : ModularCurve.relfinrank_xHHeckeCompositum_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/fc1b5761-2e50-5b97-a001-375c26172757
-- title:
--   Degree of the Hecke compositum over X_H(M) is multiplicative
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $M$ be a nonzero natural number, let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$, and let $\ell,\ell'$ be nonzero natural numbers with $\gcd(\ell,\ell')=1$. For a subgroup $\Gamma\le \mathrm{SL}_2(\mathbb{Z})$, [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) denotes the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set [`ModularCurve.intFormRatiosC`](def/ModularCurve_X1.html#L83) of ratios of $q$-expansions of integral-weight forms on $\Gamma$; here $\Gamma$ is $\Gamma_H(M)$, the subgroup [`CohCarrier.GammaH M H`](def/CohCarrier_Level.html#L133) of $\Gamma_0(M)$ cut out by the condition that the associated unit of $\mathbb{Z}/M$ lies in $H$, respectively $\Gamma_H(M)\cap\Gamma_0(t)$ for $t=M\ell$ and $t=M\ell'$. Write $K$ and $K_t$ for the intermediate fields of $L((q))$ generated over $L$ by the images of these fields under the coefficientwise map $\mathbb{Q}\to L$ ([`ModularCurve.laurentBaseChange`](def/ModularCurve_LaurentCoeff.html#L103)), and for a set $S\subseteq L((q))$ write $L(S(q^{\ell}))$ for the subfield generated over $L$ by the image of $S$ under the substitution $q\mapsto q^{\ell}$ ([`ModularCurve.qExpand`](def/ModularCurve_X0.html#L25)). The assertion is $$[\,K_{M\ell}\cdot L(K(q^{\ell}))\;(\text{i.e. } K_{M\ell}\sqcup L(K_{M\ell'}(q^{\ell})))\,:\,L(K(q^{\ell}))\,]=[\,K_{M\ell'}:K\,]\cdot[\,K_{M\ell}:L(K(q^{\ell}))\,],$$ more precisely: the relative degree of the compositum $K_{M\ell}\sqcup L(K_{M\ell'}(q^{\ell}))$ over $L(K(q^{\ell}))$ equals the product of the relative degree of $K_{M\ell'}$ over $K$ with that of $K_{M\ell}$ over $L(K(q^{\ell}))$. All three degrees are `IntermediateField.relfinrank`, the degree of the second field over its intersection with the first, as a natural number with value $0$ in the infinite case.
--
--   This is the $\Gamma_H(M)$ form of the statement that the coverings of $X_H(M)$ by $X(\Gamma_H(M)\cap\Gamma_0(M\ell))$ via $\tau\mapsto\ell\tau$ and by $X(\Gamma_H(M)\cap\Gamma_0(M\ell'))$ via the forgetful degeneracy map are linearly disjoint when $\ell$ and $\ell'$ are coprime, expressed as multiplicativity of relative degrees of the corresponding $q$-expansion function fields. It is used in the proof that Hecke operators at coprime indices on $X_H$ commute ([`ModularCurve.heckeOperatorHAlong_comm`](thm.html#ModularCurve.heckeOperatorHAlong_comm)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.relfinrank_xHHeckeCompositum_eq_mul (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (hℓ : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
          (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
            Set (LaurentSeries L))))
        (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ⊔
          IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')) :
              Set (LaurentSeries L))))
      = IntermediateField.relfinrank
            (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')))
        * IntermediateField.relfinrank
            (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
              (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
                Set (LaurentSeries L))))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by sorry
