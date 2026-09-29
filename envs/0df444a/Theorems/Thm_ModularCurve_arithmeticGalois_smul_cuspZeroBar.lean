-- Prove2me | Theorems.Thm_ModularCurve_arithmeticGalois_smul_cuspZeroBar
-- name    : ModularCurve.arithmeticGalois_smul_cuspZeroBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/3e747d53-d9e3-5e36-ac67-a326c32cc01a
-- title:
--   The cusp ̄ 0 is fixed by the arithmetic Galois action
-- statement:
--   Fix a natural number $N$ with $N \neq 0$, and let $\tau$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Write $F_0 =$ `modularFunctionFieldFull N` for the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the $q$-expansions $j(q^d)$ for the nonzero divisors $d \mid N$, and `modularFunctionFieldBar N` for its base change, namely the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the image of $F_0$ under the coefficientwise embedding. The homomorphism `arithmeticGalois` sends $\tau$ to the element of `SemilinearAut` given by the pair consisting of the ring automorphism of the base-changed field acting on Laurent series coefficient by coefficient through $\tau$, together with $\tau$ itself on $\overline{\mathbb{Q}}$; such semilinear pairs act on `Place`s (valuation subrings of the function field containing the image of $\overline{\mathbb{Q}}$, proper, and with principal ideal structure) by transport of the valuation subring. The assertion is that this action of $\tau$ fixes `cuspZeroBar N`, the place obtained by applying the base-changed Fricke involution to the $q$-expansion place at infinity. No hypothesis beyond $N \neq 0$ is imposed on $N$ or on $\tau$.
--
--   This is the rationality over $\mathbb{Q}$ of the cusp $0$ on $X_0(N)$: the point $\bar 0$, obtained from the cusp at infinity by the Fricke involution, is defined over $\mathbb{Q}$ and hence fixed by every element of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ acting arithmetically on $q$-expansion coefficients. It is used in the Mazur-style argument, in [`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`](thm.html#WeierstrassCurve.mazurStepThree_not_inZeroComponentAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_arithmeticGalois_smul_cuspZeroBar.lean

import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.arithmeticGalois_smul_cuspZeroBar (N : ℕ) [NeZero N] (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) : arithmeticGalois (modularFunctionFieldFull N) τ • cuspZeroBar N = cuspZeroBar N := by sorry
