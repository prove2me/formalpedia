-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_global_priority_zero_physical
-- name    : OAI.SevenEighths.InverseMoment.global_priority_zero_physical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:56:50.383327+00:00
-- url     : https://prove2.me/theorems/5b3ede59-a2f0-4ecf-85f8-3a32d5a85acf
-- title:
--   Bound for the global priority zero-frequency aggregate
-- statement:
--   For $\varepsilon>0$, $J_{\max}\in\mathbb N$ and $d_{\mathrm{small}}>0$ there are a finite $s\subseteq\mathbb N\times\mathbb N$ and $C_{\mathrm{zero}}>0$ such that for every family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda`, every $J_o\le J_{\max}$, `extra` with `extra x.cube` inside the cube support, `pool`, finite set `original` of valid sources with weights bounded by 1, Boolean `negative`, $\Psi$ bounded by 1, $m$, slots with pairwise disjoint lists and coefficients bounded by 1, a Schwartz $\omega$ supported in $[lo,hi]$ ($lo>0$), reals $Z\ge1$, $M,r,\ell,V,\delta,A,B\ge0,R_{\mathrm{active}},j\ge0,t,\eta,\tau$, `window` with $hi\le e^{\mathrm{window}}$, $\pi$, `height` and a nonnegative $R$, under the size bounds on the original sources ($Z^{\ell+\eta}$, $Z^{R_{\mathrm{active}}+\eta}$, $Z^{B+\eta}$, $Z^{t+\eta}$), $\ell+\eta\ge0$, $1\le Z^{\texttt{firstPhysicalHeight}+12\eta+\tau}$ and $\varepsilon(r-A-B-t)+7\eta/2+d_{\mathrm{small}}(3\ell+B+t+5\eta)+2\varepsilon(2\ell+B+t+4\eta)\le\pi+\eta/2$:
--   $$Z^{\texttt{firstKappa}(\dots)}e^{9\eta\log Z/2}\,\texttt{globalPriorityZeroAggregate}(\dots)\le C_{\mathrm{zero}}4^{|\mathrm{slots}|}\|\texttt{rowMajorant}\|_s\,\|\omega\|_{0,0}^2\,e^{\mathrm{window}(1+\varepsilon)}Z^{r+3\ell+V+17\eta+\tau+\pi},$$
--   the aggregate taken with `principalWindow` at `height`, column scale $Z^{r-A-B-t}$ and radius scale $Z^{\texttt{firstPhysicalHeight}+12\eta+\tau}$.
--
--   Lean: `OAI.SevenEighths.InverseMoment.global_priority_zero_physical` in `lean/OAI/NumberTheory/DirichletL/Descent/GlobalPriorityZeroPhysical.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion FirstCauchyArithmetic
open InverseSecondPrincipalCaller InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseMomentGlobalPrincipalMass
local notation "O"=>ActualEisensteinCubic.O

theorem global_priority_zero_physical (ε:ℝ)(hε:0<ε)(Jmax:ℕ)(dsmall:ℝ)(hdsmall:0<dsmall):
    ∃(s:Finset (ℕ×ℕ))(Czero:ℝ),0<Czero ∧
    ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (Jo:ℕ),Jo≤Jmax→∀(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
      (original:Finset (Source ι Jo))(w:Source ι Jo→ℂ)(negative:Bool)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→(∀u,‖Ψ u‖≤1)→
      (∀x∈original,‖w x‖≤1)→
    ∀(om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)
      (Z M r ell V delta A B Ractive j t eta tau window pi height:ℝ)(R:Finset ι→Finset ι→ℝ),
      1≤Z→0≤ell+eta→0≤B→0≤j→
      ε*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*ε*(2*ell+B+t+4*eta)≤pi+eta/2→
      (∀x∈original,SourceValid p x)→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))→
      (∀x∈original,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(Ractive+eta))→
      (∀x∈original,primeProductNorm p x.firstCommon≤Z^(B+eta))→
      (∀x∈original,primeProductNorm p x.quotientSupport≤Z^(t+eta))→
      (∀x∈original,extra x.cube⊆x.cube.support)→
      hi≤Real.exp window→1≤Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)→(∀G E,0≤R G E)→
      (Z^(firstKappa M r ell V delta A B Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityZeroAggregate p hg extra pool original w negative Ψ m slots lists a
        (principalWindow om lo hi hlo hs negative height) (Z^(r-A-B-t))
        (Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)) R≤
      Czero*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
        (SchwartzMap.seminorm ℝ 0 0 om)^2*Real.exp (window*(1+ε))*
        Z^(r+3*ell+V+17*eta+tau+pi):= by
  sorry
end SevenEighths.InverseMoment

end

end OAI
end
