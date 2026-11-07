-- Prove2me | Theorems.Thm_HodgeComputer_Algebra_normalDerivative_relPrime_of_specialization
-- name    : HodgeComputer.Algebra.normalDerivative_relPrime_of_specialization
-- status  : Proved
-- author  : @shivm
-- created : 2026-11-07T03:35:58.423431+00:00
-- url     : https://prove2.me/theorems/0ed75faf-c218-4f4e-ac88-566335770f26
-- title:
--   A squarefree line specialization certifies coprimality with a normal derivative
-- statement:
--   Let $K$ be a field, $n,d$ natural numbers, and $f\in K[z_0,\ldots,z_n]$ homogeneous of degree $d$. Regard $f$ as a univariate polynomial in $z_0$ with coefficients in $K[z_1,\ldots,z_n]$. Assume its coefficient of $z_0^d$ is a nonzero scalar $a\in K$. Choose $v\in K^n$ and write $p_v(t)=f(t,v)$. If $p_v$ and its formal derivative are relatively prime in $K[t]$, then
--
--   $$\operatorname{IsRelPrime}(f,\partial_{z_0}f)$$
--
--   in the full multivariate polynomial ring. Here `IsRelPrime` means that every common divisor is a unit, rather than comaximality.
--
--   The criterion reduces a multivariate denominator-admissibility check to one exact univariate computation. The nonzero top coefficient ensures that every divisor has unit leading coefficient, so its degree cannot disappear under specialization. The statement works in arbitrary characteristic; separability is supplied by the explicit relatively-prime specialization hypothesis.
-- source:
--   Derived polynomial specialization criterion. Proof uses Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474: Mathlib/Algebra/Polynomial/Eval/Degree.lean, isUnit_of_isUnit_leadingCoeff_of_isUnit_map; Mathlib/Algebra/MvPolynomial/Equiv.lean, finSuccEquiv; and formal differentiation. Applied to the hodge.computer denominator conditions.

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous


set_option autoImplicit false

theorem HodgeComputer.Algebra.normalDerivative_relPrime_of_specialization {K : Type*} [Field K] (n d : ℕ)
    (f : MvPolynomial (Fin (n + 1)) K) (a : K) (v : Fin n → K)
    (hf : f.IsHomogeneous d) (ha : a ≠ 0)
    (hc : (MvPolynomial.finSuccEquiv K n f).coeff d = MvPolynomial.C a)
    (hs : IsRelPrime ((MvPolynomial.finSuccEquiv K n f).map (MvPolynomial.eval v))
      (Polynomial.derivative ((MvPolynomial.finSuccEquiv K n f).map (MvPolynomial.eval v)))) :
    IsRelPrime f (MvPolynomial.pderiv 0 f) := by sorry
