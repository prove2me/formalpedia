-- Prove2me | Theorems.Thm_MazurProof_N13GoodPrimeSimpleRoot_multiplicity_even_of_completion_quadratic_simpleRoot
-- name    : MazurProof.N13GoodPrimeSimpleRoot.multiplicity_even_of_completion_quadratic_simpleRoot
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-09T04:39:35.643669+00:00
-- url     : https://prove2.me/theorems/369754d3-c666-452c-af19-3684dbcb87e1
-- title:
--   Mazur 13 port: multiplicity_even_of_completion_quadratic_simpleRoot
-- statement:
--   Completion form of the simple-root principle: once the global element is identified with the quadratic evaluation in the local integers, its height-one multiplicity is even.
--
--   This lemma is one step of a machine-checked proof that the genus-two curve $$Y^2 = X^6+4X^5+6X^4+2X^3+X^2+2X+1$$ (a model of $X_1(13)$) has no rational affine points other than the cusps $X\in\{0,-1\}$, which gives the case $N=13$ of Mazur's torsion theorem. The proof is Xiang Huang's Lean development, ported to this Mathlib and split into one node per large lemma; definitions live in the layered entries `MazurN13_L0`, `MazurN13_L1`, ….
-- source:
--   Xiang Huang, FLT fork, https://github.com/xiangyazi24/FLT/blob/51bbb4f/FLT/Assumptions/MazurProof/N13GoodPrimeSimpleRoot.lean#L422

import Mathlib
import Definitions.Def_MazurN13_L2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open MazurProof MazurProof.N13GoodPrimeSimpleRoot
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring

theorem MazurProof.N13GoodPrimeSimpleRoot.multiplicity_even_of_completion_quadratic_simpleRoot {A K : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [IsDedekindDomain A] (v : HeightOneSpectrum A) {global : A} (hglobal_ne : global ≠ 0) (a b c x₀ scale : v.adicCompletionIntegers K) (F V W : (v.adicCompletionIntegers K)[X]) (hglobal : algebraMap A (v.adicCompletion K) global = ((a * x₀ ^ 2 + b * x₀ + c : v.adicCompletionIntegers K) : v.adicCompletion K)) (hscale : scale ≠ 0) (hsmall : a * x₀ ^ 2 + b * x₀ + c ∈ v.completionIdeal K) (hquadDeriv : IsUnit (2 * a * x₀ + b)) (hFroot : F.eval x₀ = 0) (hFderiv : IsUnit (F.derivative.eval x₀)) (hrelation : C (scale ^ 2) * F - V ^ 2 = quadratic a b c * W) : Even (multiplicity v.asIdeal (Ideal.span {global})) := by sorry
