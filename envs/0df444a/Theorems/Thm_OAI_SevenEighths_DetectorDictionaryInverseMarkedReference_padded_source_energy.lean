-- Prove2me | Theorems.Thm_OAI_SevenEighths_DetectorDictionaryInverseMarkedReference_padded_source_energy
-- name    : OAI.SevenEighths.DetectorDictionaryInverseMarkedReference.padded_source_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:39.783745+00:00
-- url     : https://prove2.me/theorems/c6d2af30-7957-4af9-874a-7513bedb0b15
-- title:
--   Energy of the padded original source polynomials
-- statement:
--   Let $W$ be smooth with support in $[a_o,b_o]$, $0<a_o\le b_o$, $\varepsilon_m>0$, $K\in\mathbb N$. Then there are $\eta>0$ and a degree such that for every $q\ne0$ there are $C>0$, $U_0>1$ such that for all $U\ge U_0$, every finite type $\iota$ with at most $K$ elements, pairwise disjoint finite sets $L_i$ of `Supported` prime ideals outside `reflectionExcludedPrimes q`, $\ell_i\ge0$ with $N(P)/U^{\ell_i}\in[1,2]$ for $P\in L_i$, coefficients bounded by 1, weights `primeW i` supported in $[1,2]$ and nonzero at those ratios, every ideal character $\chi$ bounded by 1 such that `elementCharacter (conjugateIdealCharacter χ)` factors modulo `fixedBaseConductor q` and `conjugateIdealCharacter χ` vanishes off the excluded-prime complement, reals $0\le r$, $r-\eta\le r'\le r$ with $r+2\sum\ell_i<1$ and $2r+8\sum\ell_i<3$, finite `rows` with $\|\texttt{eisEmbedding}\,u\|^2\le U$, and $\theta$:
--   $$\sum_{u\in\mathrm{rows}}\Big\|\sum_{x\in\texttt{Tuple}\,L}\prod_i\mathrm{coeff}_i(x_i)\,\texttt{originalTotalPolynomial}(\texttt{originalSource}\,U\,r'\,b_o,\prod_ix_i,\chi,1,\texttt{childLogTest}\,W\,\theta,U,r',\textstyle\sum\ell_i,u)\Big\|^2\le C\,U^{1+\varepsilon_m}(1+|\theta|)^{2\,\mathrm{degree}}.$$
--
--   Lean: `OAI.SevenEighths.DetectorDictionaryInverseMarkedReference.padded_source_energy` in `lean/OAI/NumberTheory/DirichletL/Dictionary/InverseMarkedReferencePaddedEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure Filter
local notation "O"=>HeckeFamily.O

theorem padded_source_energy
    (W:ℝ → ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃eta:ℝ,0<eta ∧ ∃degree:ℕ,∀q:ℕ,q≠0 → ∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K →
    ∀(L:ι → Finset (Ideal O))(ell:ι → ℝ)(coeff:ι → Ideal O → ℂ),
      (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
      (∀i,∀P∈L i,Supported P) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L) →
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,‖coeff i P‖≤1) →
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P) →
    ∀(primeW:ι → ℝ → ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0) →
    ∀χ:Ideal O →*ℂ,(∀I,‖χ I‖≤1) →
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ)) →
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I →
        conjugateIdealCharacter χ I=0) →
    ∀r rr:ℝ,0≤ r → r-eta≤ rr → rr≤ r →
      r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U) → ∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U rr bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U rr (∑i,ell i) u‖^2)≤
      C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  sorry

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end
