-- Prove2me | Theorems.Thm_ModularCurve_map_eq_phiProd_lambda_of_eval_qExpand_eq_zero
-- name    : ModularCurve.map_eq_phiProd_lambda_of_eval_qExpand_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/0b3c9663-ecca-5cbe-b44a-6a9a62a26b8b
-- title:
--   Level-two modular relation splits into q+1 conjugates
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $q$ be a prime, and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $q$-th root of unity. Write $\lambda$ for the Laurent series `lambdaModC`, the coefficientwise image under $\mathbb{Z}\to L$ of the integral series $t\cdot\eta^{8}\cdot\eta^{16}(t^{4})\cdot(\eta\text{-unit inverse})(t^{2})$ built from `etaProd` and `dedekindEtaUnitInv`; write $f\mapsto f(t^{N})$ for `qExpand L N`, the substitution obtained by multiplying exponents by $N$, and $f\mapsto f(ut)$ for `qTwist u`, multiplication of the coefficient of $t^{k}$ by $u^{k}$. Let $P$ be a monic polynomial over $\mathbb{Q}((t))$ with `natDegree` equal to $q+1$ such that $P(\lambda(t^{q}))=0$, and such that the polynomial obtained from $P$ by applying $t\mapsto t^{q}$ to each coefficient vanishes at $\lambda(t)$. Then, after applying to the coefficients of $P$ the substitution $t\mapsto t^{q}$ followed by the coefficientwise embedding $\mathbb{Q}((t))\to K((t))$ induced by $\mathbb{Q}\to K$, the resulting polynomial in $K((t))[X]$ equals the product `phiProd` of the $q+1$ linear factors $X-\lambda(t^{q^{2}})$ and $X-\lambda(\zeta^{b}t)$ for $b=0,\dots,q-1$, in this order as a family indexed by $\mathrm{Fin}(q+1)$ via `Fin.cons`.
--
--   This is the level-two form of the classical statement that the modular equation of prime level $q$ splits over $K((t))$ into the $q+1$ conjugate factors, here with Legendre's normalised $\lambda$-series in place of $j$ and the conjugates listed with the spread conjugate $\lambda(t^{q^{2}})$ first, followed by the $q$ twists $\lambda(\zeta^{b}t)$. It is used to control the coefficients of the minimal polynomial of $\lambda(t^{q})$, in [`ModularCurve.intCoeffs_minpoly_lambdaNModC_coeff`](thm.html#ModularCurve.intCoeffs_minpoly_lambdaNModC_coeff) and [`ModularCurve.minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg`](thm.html#ModularCurve.minpoly_lambdaNModC_coeff_coeff_eq_zero_of_neg).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_map_eq_phiProd_lambda_of_eval_qExpand_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.map_eq_phiProd_lambda_of_eval_qExpand_eq_zero
    {K : Type*} [Field K] [Algebra ℚ K] (q : ℕ) [Fact q.Prime] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) q)
    (P : Polynomial (LaurentSeries ℚ)) (hP : P.Monic) (hdeg : P.natDegree = q + 1)
    (h0 : P.eval (lambdaNModC ℚ q) = 0)
    (h1 : (P.map (qExpand ℚ q)).eval (lambdaModC ℚ) = 0) :
    P.map ((coeffEmb K).comp (qExpand ℚ q)) =
      phiProd q (Fin.cons (qExpand K (q * q) (lambdaModC K))
        (fun b : Fin q => qTwist (ζ ^ (b : ℕ)) (lambdaModC K)) : Fin (q + 1) → LaurentSeries K) := by sorry
