-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseInitialTotalRows_original_input_rows_fourier_bound
-- name    : OAI.SevenEighths.InverseInitialTotalRows.original_input_rows_fourier_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:11:27.461784+00:00
-- url     : https://prove2.me/theorems/766b18b8-3119-4d4b-9886-5f61dede56b8
-- title:
--   Fourier-twisted input rows bound
-- statement:
--   Let $W$ be smooth with support in $[a_0,b_0]$ ($a_0>0$) and bounded by $B_0\ge0$, $b_{\mathrm{cap}}\ge1$, $\Phi$ Schwartz with $\operatorname{Re}\Phi\ge0$ and $\Phi=1$ on $[0,1]$, and reals $\mathrm{cap}\ge0$, `gap`, $\varepsilon,\pi,\eta,\tau$, `loss` positive with $\eta\le1$, $\eta,\tau\le\mathrm{gap}/50$, $K\in\mathbb N$. Then there are a degree and $B_{\mathrm{tree}}\ge1$ such that for every $q\ne0$ there are $C>0$, $Z_0>1$ such that for all $Z\ge Z_0$, $D_{\mathrm{pool}}\ge B_{\mathrm{tree}}Z^{\mathrm{cap}+1}$, slot data with assigned elements as in the finite physical bound, $\Psi$ bounded by 1 factoring modulo `fixedBaseConductor q`, reals $D,m,r$ with the center constraints, finite `rows` with $\|\texttt{eisEmbedding}\,u\|^2\le Z^m$, phases $y$ and $\theta$:
--   $$\sum_{u\in\mathrm{rows}}\big\|Z^{-D/2}\,\texttt{inputConjugateRow}\,p\dots\Psi\,(\texttt{assignedElement})\,1\,1\,(\texttt{initialTest}\,p\,(\texttt{primeMark}(\mathrm{all}\setminus\mathrm{assigned})\,(\mathrm{coeff}\cdot\texttt{logPhase}(-\theta)\,y))\,(\texttt{childLogTest}\,W\,\theta)\,Z\,D)\,u\big\|^2\le C\,Z^{m+15\eta+\pi+\varepsilon+\mathrm{loss}}(1+|\theta|)^{2\,\mathrm{degree}}.$$
--
--   Lean: `OAI.SevenEighths.InverseInitialTotalRows.original_input_rows_fourier_bound` in `lean/OAI/NumberTheory/DirichletL/Inversion/InitialTotalRows.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalRows
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
theorem original_input_rows_fourier_bound
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤ cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤ m→m≤ cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤ m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤ cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(θ:ℝ),
      (∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)))
            (childLogTest W θ) Z D) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  sorry

end SevenEighths.InverseInitialTotalRows

end

end OAI
end
