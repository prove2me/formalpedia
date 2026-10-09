-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_marked_bin_height
-- name    : OAI.SevenEighths.InverseMoment.actual_marked_bin_height
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:45.510985+00:00
-- url     : https://prove2.me/theorems/3d3f85b1-346d-4fa5-a24b-5f4248da222c
-- title:
--   Energy of marked reopened cube bins from child bounds
-- statement:
--   Let $W$ be smooth with support in $[a_0,b_0]$ ($a_0>0$, $b_0\ge0$), $V_{\log}$ Schwartz vanishing outside $[-A_{\log},A_{\log}]$ and equal to 1 on $[-\rho,\rho]$ with $\rho=$`columnWindowRadius a₀ b₀`, reals $L_{\mathrm{cap}}\ge0$, $0\le\eta\le1$, $0<\tau\le1$, `saving`, $e_m,e_d>0$ and $K\in\mathbb N$. Then there are four compactly supported Schwartz functions $\omega_{11},\omega_{12}$ (support in $[a_{f1},b_{f1}]$) and $\omega_{21},\omega_{22}$ (support in $[a_{f2},b_{f2}]$), with $0<a_{fi}\le b_{fi}$, and reals `window`, $b_w=e^{\mathrm{window}}\ge\max(1,e^{A_{\log}})$, such that for all $\varepsilon_{\mathrm{First}},\varepsilon_{\mathrm{Second}}>0$ and `degree` there are $C_{\mathrm{coef}}>0$, $C\ge0$ such that for every $\theta$, every finite set $S$ of prime ideals containing `fixedBadPrimes` and $D\in\mathbb N$ (with $F=$`outsideSquarefreeIdeals S D`, its pool `poolPrimary F` and $\omega=$`radialFromLog Vlog`), every finite $Q$ of exponent vectors, squarefree nonzero `labels` of norm $\le Z^{V+\eta}$, $\Psi$ bounded by 1, $m$, at most $K$ slots with pairwise disjoint lists and weights bounded by 1, and reals $Z,M,r,\ell,V,H_0,\pi,\varepsilon_{\mathrm{child}},A,\mathrm{loss},\mathrm{loss}_{\mathrm{Final}}$ satisfying the numerical constraints of the Lean (cube norms in $[Z^\ell,eZ^\ell]$, $b_0Z^{r+3\ell}\le D$, $r+3\ell+V\le L_{\mathrm{cap}}$, the budget inequalities for loss and $\mathrm{loss}_{\mathrm{Final}}$, …), if `ChildBounds` holds with $(\omega_{11},\omega_{12})$ for `negative = true` and with $(\omega_{21},\omega_{22})$ for `negative = false` at every key of `actualLongSourceKeys` and every $\xi$, then
--   $$Z^{-V}\,\texttt{rowFamilyEnergy}\big(\texttt{labels},\ \texttt{markedReopenedCubeBin}\,S\,D\,Q\,\Psi\,m\,I_{\mathrm{gen}}\,z\,(\texttt{normTwistedSource}\,W\,\theta)\,Z^{r+3\ell}\,H_0\dots,\ Z^M\big)\le C\big(C_{\mathrm{coef}}(eZ^\ell)^{\varepsilon_{\mathrm{First}}}\big)^2(1+A)Z^{r+3\ell+V+\mathrm{loss}_{\mathrm{Final}}}(1+|\theta|)^{2(k+n)},$$
--   with $k=$`momentOrder (firstDegree degree)` and $n$ the `integrablePower` of Lebesgue measure.
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_marked_bin_height` in `lean/OAI/NumberTheory/DirichletL/Descent/CanonicalLongHeightBin.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstLabelCell InverseMomentFirstSecondHeightCost CompletedHeight
open FourierBridge JointLogSeparation
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_bin_height
    (a₀ b₀:ℝ)(ha₀:0<a₀)(hb₀:0≤b₀)
    (W:ℝ→ℂ)(hsW:Function.support W⊆Set.Icc a₀ b₀)(hW:ContDiff ℝ ∞ W)
    (Vlog:𝓢(ℝ,ℂ))(Alog:ℝ)(hbox:∀x,Vlog x≠0 → |x|≤Alog)
    (hone:∀x,|x|≤CanonicalCubeSeparation.columnWindowRadius a₀ b₀ → Vlog x=1)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ → ℂ) ∧ HasCompactSupport (ω₁₂:ℝ → ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂₂:ℝ → ℂ) ∧
      tsupport (ω₁₁:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ → ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ → ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ Real.exp Alog≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst → 0<epsSecond → ∀degree:ℕ,
      ∃Ccoef C:ℝ,0<Ccoef ∧ 0≤C ∧
    ∀theta:ℝ,
    ∀{σ:Type}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P),
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      let p:=poolPrimary F;
      let hp:=poolPrimary_ne_zero F hF;
      let hcop:=poolPrimary_coprime F hF;
      let hg:=poolPrimary_good F hF;
      let om:=radialFromLog Vlog (Vlog.smooth ⊤) Alog hbox;
      ∀(Q:Finset (primePool F →₀ ℕ))(labels:Finset (Ideal O))(Ψ:O →* ℂ)(m:O)
        (slots:Finset σ)(lists:σ → Finset (primePool F))(weights:σ → primePool F → ℂ)
        (Z M r ell V H₀ pi epschild A loss lossFinal:ℝ),
        2≤Z → 2≤Z^eta → Real.exp 1≤Z^eta → 0≤M → r+3*ell+V≤Lcap → M≤Lcap →
        0≤ell → 0≤V → -eta≤ r → Real.exp Alog≤Z^eta →
        (∀v∈Q,Z^ell≤(Ideal.absNorm (cubeIdeal F v):ℝ)) →
        (∀v∈Q,(Ideal.absNorm (cubeIdeal F v):ℝ)≤Real.exp 1*Z^ell) →
        r≤Lcap → ell≤Lcap → V≤Lcap → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
        em*(20*(3*Lcap+16)+30)≤pi/4 → ed*(20*(3*Lcap+16)+30)≤pi/4 →
        0≤epschild → -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond →
        48*eta+tau+pi+epschild+epsSecond≤loss → slots.card≤K →
        M-ell≤ r+3*ell+V → 3*eta+epsFirst*(5*ell+2*r+7*eta)≤lossFinal →
        loss+(2*Lcap+15*eta+tau)*epsFirst+epsFirst≤lossFinal → -saving≤ r+3*ell+V+lossFinal →
        (∀u,‖Ψ u‖≤1) → 0≤A → (∀I∈labels,Squarefree I) → (∀I∈labels,I≠0) →
        (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
        (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) →
        b₀*Z^(r+3*ell)≤D →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
            Z M r ell V eta tau window bw epschild A K degree) →
        (∀ξ:ℝ,∀k∈actualLongSourceKeys p hp hcop hg Finset.univ Q labels Ψ m (m*excludedGenerator S)
          slots lists weights om Z M r ell V H₀ ξ Lcap eta tau,
          ChildBounds p hp hcop hg Finset.univ Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
            Z M r ell V eta tau window bw epschild A K degree) →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z
          (normTwistedSource W theta) (Z^(r+3*ell)) H₀ slots lists weights) (Z^M)≤
          C*(Ccoef*(Real.exp 1*Z^ell)^epsFirst)^2*(1+A)*Z^(r+3*ell+V+lossFinal)*
            (1+‖theta‖)^(2*(InverseClippingProfiles.momentOrder (firstDegree degree)+(volume:Measure ℝ).integrablePower)) := by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
