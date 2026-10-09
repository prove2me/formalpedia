-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_complete_state_from_rank_moments
-- name    : OAI.SevenEighths.InverseMoment.actual_complete_state_from_rank_moments
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:10:24.680987+00:00
-- url     : https://prove2.me/theorems/8fe51f04-2566-4480-9592-fede7af34841
-- title:
--   Complete canonical rows bounded from rank moments
-- statement:
--   Let $W$ be smooth with support in $[lo,hi]$ ($lo>0$, $hi\ge0$), $V_{\log}$ Schwartz vanishing outside $[-A_{\log},A_{\log}]$ and equal to 1 on $[-\rho,\rho]$, $\rho=$`columnWindowRadius lo hi`, reals $L\ge1$, $c^*>0$, $0<\eta\le\min(1,c^*/100000)$, $0<\tau\le1$, `saving`, $e_m,e_d,\varepsilon>0$ and $K\in\mathbb N$. Then there are four compactly supported Schwartz functions $\omega_{11},\omega_{12},\omega_{21},\omega_{22}$ (supports in $[a_{f1},b_{f1}]$, $[a_{f2},b_{f2}]$, $0<a_{fi}\le b_{fi}$), reals `window`, $b_w=e^{\mathrm{window}}\ge\max(1,e^{A_{\log}})$ and a short degree such that for all $\varepsilon_{\mathrm{First}},\varepsilon_{\mathrm{Second}}>0$, every degree and every $q\ne0$ there are $C_s>0$, $C_b\ge0$, $Z_0>1$ with the following property. For every slot type, $m\ne0$ and reals $Z,N,V,M,z_0$, `margin`, `cutoff`, $\pi$, $\varepsilon_{\mathrm{child}}$, $A$, `loss`, $\mathrm{loss}_{\mathrm{Final}}$, $\theta$ satisfying the numerical hypotheses of the Lean ($Z\ge Z_0$, $Z\ge2$, $Z^\eta\ge\max(2,e)$, $\eta\log Z\ge1$, $0\le N,V,M$, $N+V\le L$, $M\le N+V$, $z_0\le L$, $hi,e^{A_{\log}},e^{\mathrm{window}}\le Z^\eta$, $0<\mathrm{cutoff}\le\min(L,c^*/200)$, $\eta\le\mathrm{cutoff}/32$, $N((m))\le Z^L$, `CanonicalMargins (N+V) M (normWidth Z (m)) z₀ margin` with margin $\ge c^*/2$, radical of $(m)$ of norm $\le Z^{\texttt{normWidth}}$, the budgets for $\pi$, loss and $\mathrm{loss}_{\mathrm{Final}}$, $A\ge0$), every finite set of `Supported` squarefree `labels` of norm $\le Z^V$, $D\ge hi\,Z^N$, at most $K$ slots with pairwise disjoint lists of primes of norm $\le H_i$ ($H_i\ge1$, $\prod H_i\le Z^{z_0}$) and coefficients bounded by 1, every base ray twist $\Psi$ of `base` bounded by 1 and factoring modulo `fixedBaseConductor q`: if `CanonicalRankMoments` holds for each of the four $\omega_{ij}$ (at $Z$, $M-\tfrac34\mathrm{cutoff}$, $N+V+15\eta$, $z_0$, $\mathrm{margin}-7\eta$, $\varepsilon_{\mathrm{child}}$, $A$, $K$, degree), then
--   $$Z^{-(N+V)}\sum_{I\in\mathrm{labels}}\texttt{secondLabelWeight}\,K\,I\sum_{z}\|\texttt{outsideCanonicalMarkedRow}\,S\,D\dots\Psi\,m\,I_{\mathrm{gen}}\,z\dots(\texttt{normTwistedSource}\,W\,\theta)\,Z^N\|^2\le C_s(1+|\theta|)^{\mathrm{shortDegree}}Z^{N+V-c^*/256}+C_b(1+A)(1+|\theta|)^{2(k+n)}Z^{N+V+\mathrm{loss}_{\mathrm{Final}}+2L\varepsilon_{\mathrm{First}}+\varepsilon},$$
--   with $S=$`reflectionExcludedPrimes q`, $z$ over `nonzeroChildFrequencyBall 1 (Z^M)`, $k=$`momentOrder (firstDegree degree)` and $n$ the `integrablePower` of Lebesgue measure.
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_complete_state_from_rank_moments` in `lean/OAI/NumberTheory/DirichletL/Descent/CanonicalCompleteRank.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation InverseReflectedPhase InverseTerminalWidths InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_state_from_rank_moments
    (lo hi:ℝ)(hlo:0<lo)(hhi:0≤hi)(W:ℝ→ℂ)
    (hsW:Function.support W⊆Set.Icc lo hi)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤ columnWindowRadius lo hi → Vlog x=1)
    (L cstar eta tau saving em ed eps:ℝ)(hL:1≤L)(hcstar:0<cstar)(heta:0<eta)
    (heta1:eta≤1)(hetac:eta≤ cstar/100000)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(heps:0<eps)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ)(shortDegree:ℕ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
    ∀(q:ℕ)(hq:q≠0),∃Cs Cb Z₀:ℝ,0<Cs ∧ 0≤Cb ∧ 1<Z₀ ∧
    ∀{σ:Type}[DecidableEq σ](m:O),m≠0 →
    ∀Z N V M z₀ margin cutoff pi epschild A loss lossFinal theta:ℝ,
      Z₀≤Z → 2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 1≤eta*Real.log Z →
      0≤N → 0≤V → 0≤M → N+V≤L → M≤N+V → z₀≤L →
      hi≤Z^eta → Real.exp Alog≤Z^eta → Real.exp window≤Z^eta →
      0<cutoff → cutoff≤L → cutoff≤ cstar/200 → eta≤ cutoff/32 →
      (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤ margin →
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^(normWidth Z (Ideal.span {m})) →
      0≤pi → 6*eta≤pi → em*(20*(3*L+16)+30)≤pi/4 → ed*(20*(3*L+16)+30)≤pi/4 →
      0≤epschild → -saving≤48*eta+tau+pi+epschild+epsSecond →
      48*eta+tau+pi+epschild+epsSecond≤loss →
      3*eta+epsFirst*(2*L+7*eta)≤lossFinal →
      loss+(2*L+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤lossFinal →
      0≤A →
    ∀labels:Finset (Ideal O),(∀I∈labels,Supported I ∧ Squarefree I ∧ (I.absNorm:ℝ)≤Z^V) →
    ∀D:ℕ,hi*Z^N≤D → ∀slots:Finset σ,slots.card≤K →
    ∀(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))(H:σ→ℝ),
      (slots:Set σ).PairwiseDisjoint lists →
      (∀i∈slots,1≤H i) → (∀i∈slots,∀P∈lists i,(Ideal.absNorm P.val:ℝ)≤H i) → (∏i∈slots,H i)≤Z^z₀ →
    ∀(base Ψ:O→*ℂ),CanonicalCoefficientClass.IsBaseRayTwist base Ψ → (∀u,‖Ψ u‖≤1) →
      CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ,
      (∀i∈slots,∀P∈lists i,‖a i P‖≤1) →
      let S:=reflectionExcludedPrimes q;
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q);
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let _om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₁₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₁
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      CanonicalRankMoments (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ base slots lists a ω₂₂
        Z (M-3*(cutoff/2)/2) (N+V+15*eta) z₀ (margin-7*eta) epschild A K degree →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 (Z^M),
        ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) z
          slots lists a (normTwistedSource W theta) (Z^N)‖^2)≤
      Cs*(1+‖theta‖)^shortDegree*Z^(N+V-cstar/256)+
      Cb*(1+A)*(1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower))*
        Z^(N+V+lossFinal+2*L*epsFirst+eps) := by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
