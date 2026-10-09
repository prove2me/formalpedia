-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseInitialExcludedFourier_original_tuples_excluded_fourier
-- name    : OAI.SevenEighths.InverseInitialExcludedFourier.original_tuples_excluded_fourier
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T23:47:58.083336+00:00
-- url     : https://prove2.me/theorems/e9faf3b9-b3d8-468e-aa47-afc32443a3ca
-- title:
--   Fourier expansion of the excluded original tuples
-- statement:
--   Let $W,w_{\mathrm{Fresh}}:\mathbb R\to\mathbb C$ with $W$ smooth and supported in $[a_0,b_0]$, $a_0>0$; $E$ a finite set of prime ideals of the Eisenstein integers; $I$ a finite slot set with lists $L_i$ of prime ideals and coefficients $a_i$; $j\ne0$ an ideal such that for every choice $q\in I.\mathrm{pi}\,L$ the ideal $j\cdot$`survivingProduct I q` is `Admissible`, its chosen primes are pairwise coprime, and it is `outside E`; $\eta$ a multiplicative map on ideals vanishing off `outside E`; $u\in\mathcal O$; reals $Z>0$, $r,z,G$; $\ell,lo,hi:\sigma\to\mathbb R$ with $\sum_{i\in I}\ell_i=z-G$; $j_{lo},j_{hi}$ with $N(j)/Z^G\in[j_{lo},j_{hi}]$; nonzero coefficients only at primes whose `slotRatio` lies in $[lo_i,hi_i]$; $w_{\mathrm{Fresh}}=1$ wherever it is needed by $W$ (hypothesis `hFresh`); and a finite set $F$ of `Admissible` ideals outside $E$ containing the relevant `tupleColumns`. Then, with $S=$`originalSource Z r b₀`, the sum over $q$ of $\prod_ia_i(q_i)$ times `residualNormalizedPolynomial S (j·survivingProduct I q) j η 1 W Z r z G u` equals
--   $$\int_{\mathbb R}\texttt{density}(\texttt{logSchwartz}\,W)\big(\log(N(j)/Z^G)\big)(t)\cdot Z^{-(r+z-2G)/2}\cdot\texttt{inputConjugateRow}(\dots,\texttt{initialTest}(\dots,\texttt{childLogTest}\,w_{\mathrm{Fresh}}\,t,\dots),u)\,dt,$$
--   the integrand's row being built from `poolPrimary F`, `elementCharacter η`, `primaryGenerator j` and the marks $a_i(q)\,$`logPhase (-t) (log (slotRatio …))`.
--
--   Lean: `OAI.SevenEighths.InverseInitialExcludedFourier.original_tuples_excluded_fourier` in `lean/OAI/NumberTheory/DirichletL/Inversion/InitialExcludedFourier.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B012

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
open ConcretePrimeRowBridge FirstCauchyArithmetic SecondPassArithmetic FirstPassCubeLabels
namespace SevenEighths.InverseInitialExcludedFourier
open InverseMoment InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonProfile
open InverseInitialCommonCutoff InverseInitialCommonTuples InverseInitialOverlapFourier
open InverseInitialRayAttachment InverseInitialArithmetic
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialKernelBridge
open InverseInitialEnergyCallerWindow
local notation "Eis"=>ActualEisensteinCubic.O
variable {σ:Type*} [DecidableEq σ]

open InverseInitialExcludedPool
theorem original_tuples_excluded_fourier
    (W wFresh:ℝ→ℂ)(a₀ b₀:ℝ)(ha₀:0<a₀)
    (hs:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (E:Finset (Ideal Eis))(hE:∀Q∈E,Prime Q)
    (I:Finset σ)(L:σ→Finset (Ideal Eis))(hL:∀i∈I,∀P∈L i,Prime P)
    (a:σ→Ideal Eis→ℂ)(j:Ideal Eis)(hj0:j≠0)
    (hP:∀q∈I.pi L,Admissible (j*survivingProduct I q))
    (hcop:∀q∈I.pi L,Pairwise (Function.onFun IsCoprime (fun i:I=>q i.val i.property)))
    (hPE:∀q∈I.pi L,outside E (j*survivingProduct I q))
    (η:Ideal Eis→*ℂ)(hη:∀c,¬outside E c→η c=0)(u:Eis)(Z r z G:ℝ)(hZ:0<Z)(ell lo hi:σ→ℝ)
    (hell:∑i∈I,ell i=z-G)(jlo jhi:ℝ)
    (hj:((j.absNorm:ℝ)/Z^G)∈Set.Icc jlo jhi)
    (ha:∀i∈I,∀q∈L i,a i q≠0→slotRatio Z ell i q∈Set.Icc (lo i) (hi i))
    (hFresh:∀(v:σ→ℝ)(yj yc:ℝ),(∀i∈I,v i∈Set.Icc (lo i) (hi i))→
      yj∈Set.Icc jlo jhi→0<yc→W (yj*yc/(∏i∈I,v i))≠0→wFresh yc=1)
    (F:Finset (Ideal Eis))(hF:∀c∈F,Admissible c)(hFE:∀c∈F,outside E c)
    (hsub:tupleColumns (originalOutside (originalSource Z r b₀) E) (I.pi L)
      (fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q) j⊆F) :
    let S := originalSource Z r b₀
    let P := fun q:∀i∈I,Ideal Eis=>j*survivingProduct I q
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    (∑q∈I.pi L,(∏i∈I.attach,a i.val (q i.val i.property))*
      residualNormalizedPolynomial S (P q) j η (fun _=>1) W Z r z G u)=
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW)
        (Real.log ((j.absNorm:ℝ)/Z^G)) t*
        (((Z^(-(r+z-2*G)/2):ℝ):ℂ)*inputConjugateRow
          (poolPrimary F) (poolPrimary_good F hF) Finset.univ
          (elementCharacter η) (primaryGenerator j) 1 1
          (initialTest (poolPrimary F)
            (primeMark I (fun i=>poolList F (L i))
              (fun i q=>a i q.val*logPhase (-t) (Real.log (slotRatio Z ell i q.val))))
            (childLogTest wFresh t) Z (r+z-2*G)) u) := by
  sorry

end SevenEighths.InverseInitialExcludedFourier

end

end OAI
end
