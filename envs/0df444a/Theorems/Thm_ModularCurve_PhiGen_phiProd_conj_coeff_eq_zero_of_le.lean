-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le
-- name    : ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/7c7804df-0623-5cbc-97b2-60df6540bc6b
-- title:
--   Pole bound for the non-constant coefficients of phiProd
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a prime natural number, and let $\zeta$ be a unit of $K$. For $i$ in $\mathrm{Fin}(\ell+1)$ put $a_i = \ell$ and $b_i = 0$ when $i = 0$, and $a_i = 1$ and $b_i = i - 1$ otherwise, and let $\mathrm{conj}\,\ell\,\zeta\,i$ be the Laurent series over $K$ obtained from the rational Laurent series `jq`, pushed forward coefficientwise along $\mathbb{Q} \to K$, by applying `qTwist (ζ ^ (a * b))` followed by `qExpand K (a * a)` with $a = a_i$, $b = b_i$. Let $\mathrm{phiProd}\,\ell\,(\mathrm{conj}\,\ell\,\zeta) = \prod_{i} (X - C(\mathrm{conj}\,\ell\,\zeta\,i))$ be the corresponding monic polynomial of degree $\ell+1$ in $X$ with coefficients in the field of Laurent series over $K$. Then for every natural number $k \neq 0$ and every natural number $m$ with $\ell^2 + \ell \le m$, the coefficient of $t^{-m}$ in the $X^k$-coefficient of this product vanishes.
--
--   This is the coefficientwise form of the bound on the order of the pole at the cusp of the non-leading coefficients of the modular-equation-type polynomial $\prod_i (X - \mathrm{conj}\,\ell\,\zeta\,i)$: each such coefficient, a Laurent series in $t$, has pole order strictly less than $\ell^2 + \ell$. It supplies the degree input used by [`ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq`](thm.html#ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq) when the symmetric functions of the conjugates are expressed through the $j$-series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_eq_zero_of_le.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) (m : ℕ) (hm : ℓ * ℓ + ℓ ≤ m) : ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff (-(m : ℤ)) = 0 := by sorry
