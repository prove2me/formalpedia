-- Prove2me | Theorems.Thm_ModularCurve_lambdaEval_kroneckerRemainder
-- name    : ModularCurve.lambdaEval_kroneckerRemainder
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/1540c539-d1e5-51fa-a95f-dab264277ad1
-- title:
--   Kronecker remainder of the λ-modular equation, evaluated
-- statement:
--   Let $q$ be a prime and let `data` be a `LambdaModularPolynomialData q`: a polynomial $\Psi \in (\mathbb{Z}[X])[Y]$ that is monic of degree $q+1$ in $Y$ and satisfies $\Psi = 0$ when its coefficients in $\mathbb{Z}[X]$ are evaluated by the homomorphism $\mathbb{Z}[X] \to \mathbb{Q}(\!(q)\!)$ sending $X$ to the Laurent series `lambdaInt` (the explicit eta-quotient $q$-expansion of the Legendre $\lambda$-function) pushed forward to $\mathbb{Q}$, and $Y$ is sent to `lambdaNModC ℚ q`, the series obtained from it by multiplying all exponents by $q$. Let $R \in (\mathbb{Z}[X])[Y]$ be such that Kronecker's form $\Psi = (X^{q} - Y)(X - Y^{q}) + q\,R$ holds, where $X$ denotes the constant coefficient $\mathrm{C}\,X$ and $Y$ the outer variable. Let $L$ be a field with a $\mathbb{Q}$-algebra structure and $A \subseteq L$ a subring. Transport $R$ to $A[X_0, X_1]$ by mapping integer coefficients into $A$, the inner variable to $X_0$ and the outer variable to $X_1$, and evaluate by `lambdaEval q A`, the homomorphism $A[X_0,X_1] \to L(\!(q)\!)$ sending constants through $A \hookrightarrow L \hookrightarrow L(\!(q)\!)$, $X_0 \mapsto$ `lambdaModC L` and $X_1 \mapsto$ `lambdaNModC L q`. Then the resulting Laurent series equals the inverse of the image of $q$ in $L(\!(q)\!)$ times $(\lambda_q - \lambda^{q})(\lambda - \lambda_q^{q})$, where $\lambda =$ `lambdaModC L` and $\lambda_q =$ `lambdaNModC L q`.
--
--   This is the level-two ($\lambda$-line) form of the evaluation of Kronecker's remainder term in the modular equation: the defect of the congruence $\Psi \equiv (X^q - Y)(X - Y^q) \bmod q$, evaluated at the pair of $q$-expansions, is computed explicitly in $L(\!(q)\!)$. It is used in the analysis of the node of the $\lambda$-model, feeding the identification of the completed local ring with a $uv$-crossing model and the integral closedness of the associated coefficient subring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_lambdaEval_kroneckerRemainder.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaModularPolynomialData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.LambdaNodeLocalized

theorem ModularCurve.lambdaEval_kroneckerRemainder
    {q : ℕ} [Fact q.Prime] (data : LambdaModularPolynomialData q) (R : Polynomial (Polynomial ℤ))
    (hR : data.Ψ = (Polynomial.C Polynomial.X ^ q - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ q)
      + Polynomial.C (Polynomial.C (q : ℤ)) * R)
    {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L) :
    lambdaEval q A
        (Polynomial.eval₂ (Polynomial.eval₂RingHom (MvPolynomial.C.comp (Int.castRingHom A)) (MvPolynomial.X 0))
          (MvPolynomial.X 1) R : MvPolynomial (Fin 2) A)
      = (algebraMap L (LaurentSeries L) (q : L))⁻¹
        * ((lambdaNModC L q - lambdaModC L ^ q) * (lambdaModC L - lambdaNModC L q ^ q)) := by sorry
