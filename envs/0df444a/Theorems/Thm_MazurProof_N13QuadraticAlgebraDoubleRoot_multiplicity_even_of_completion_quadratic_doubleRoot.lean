-- Prove2me | Theorems.Thm_MazurProof_N13QuadraticAlgebraDoubleRoot_multiplicity_even_of_completion_quadratic_doubleRoot
-- name    : MazurProof.N13QuadraticAlgebraDoubleRoot.multiplicity_even_of_completion_quadratic_doubleRoot
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T05:16:32.362666+00:00
-- url     : https://prove2.me/theorems/751b19e1-fab4-41e1-be7d-5e2896a5154f
-- title:
--   Mazur 13 port: multiplicity_even_of_completion_quadratic_doubleRoot
-- statement:
--   Supporting lemma `multiplicity_even_of_completion_quadratic_doubleRoot` (namespace `MazurProof.N13QuadraticAlgebraDoubleRoot`).
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13QuadraticAlgebraDoubleRoot.lean#L461

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13QuadraticAlgebraDoubleRoot
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open N13GoodPrimeSimpleRoot

theorem MazurProof.N13QuadraticAlgebraDoubleRoot.multiplicity_even_of_completion_quadratic_doubleRoot {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsDedekindDomain A] (v : IsDedekindDomain.HeightOneSpectrum A) {global : A} (hglobal_ne : global ≠ 0) (a b c x scale : v.adicCompletionIntegers K) (F V W : (v.adicCompletionIntegers K)[X]) (hglobal : algebraMap A (v.adicCompletion K) global = ((a * x ^ 2 + b * x + c : v.adicCompletionIntegers K) : v.adicCompletion K)) (hscale : scale ≠ 0) (ha : IsUnit a) (hsmall : a * x ^ 2 + b * x + c ∈ v.completionIdeal K) (hnonsimple : ¬ IsUnit (2 * a * x + b)) (hFroot : F.eval x = 0) (hFderiv : IsUnit (F.derivative.eval x)) (hrelation : Polynomial.C (scale ^ 2) * F - V ^ 2 = quadratic a b c * W) : Even (multiplicity v.asIdeal (Ideal.span {global})) := by sorry
