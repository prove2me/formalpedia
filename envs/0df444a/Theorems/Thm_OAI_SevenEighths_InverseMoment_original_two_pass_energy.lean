-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_original_two_pass_energy
-- name    : OAI.SevenEighths.InverseMoment.original_two_pass_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:36.18907+00:00
-- url     : https://prove2.me/theorems/9562f231-e8b4-4edd-bcb1-a7461b588138
-- title:
--   Two-pass bound for the original reopened row energy
-- statement:
--   Let $\omega$ be a Schwartz function supported in $[a,b]$ ($a>0$, $b\ge0$), and reals $L_{\mathrm{cap}}\ge0$, $0\le\eta\le1$, $0<\tau\le1$, `saving`, $e_m,e_d>0$, $K\in\mathbb N$. Then there are four compactly supported Schwartz functions $\omega_{11},\omega_{12}$ (support in $[a_{f1},b_{f1}]$), $\omega_{21},\omega_{22}$ (support in $[a_{f2},b_{f2}]$), $0<a_{fi}\le b_{fi}$, and reals `window`, $b_w=e^{\mathrm{window}}\ge\max(1,b)$, such that for all $\varepsilon_{\mathrm{First}},\varepsilon_{\mathrm{Second}}>0$ and `degree` there are $C,C_{\mathrm{zero}},C_{\mathrm{tail}}\ge0$ with the following property. For every family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` (residue characteristic $\ne2$, `goodLambda`$^2\mid p_i-1$), `pool`, finite $Q$ supported in `pool` with cube primary products $\le Z^{\ell+\eta}$, squarefree nonzero `labels` of norm $\le Z^{V+\eta}$, coefficients $\beta$ bounded by $\Gamma\ge0$, $\Psi$ bounded by 1, $m$, at most $K$ slots with pairwise disjoint lists and weights bounded by 1, and reals $Z\ge2$, $Z^\eta\ge2$, $M\ge0$, $r,\ell,V,M\le L_{\mathrm{cap}}$, $r+3\ell+V\le L_{\mathrm{cap}}$, $\ell,V\ge0$, $-\eta\le r$, $b\le Z^\eta$, $e^{\mathrm{window}}\le Z^\eta$, $\pi\ge6\eta$, the two cost conditions $e_m(20(3L_{\mathrm{cap}}+16)+30)\le\pi/4$ (and for $e_d$), $\varepsilon_{\mathrm{child}}\ge0$, $A\ge0$, $-\mathrm{saving}\le r+3\ell+V+48\eta+\tau+\pi+\varepsilon_{\mathrm{child}}+\varepsilon_{\mathrm{Second}}$ and $48\eta+\tau+\pi+\varepsilon_{\mathrm{child}}+\varepsilon_{\mathrm{Second}}\le\mathrm{loss}$, $\theta$: if `ChildBounds` holds with $(\omega_{11},\omega_{12})$ for `negative = true` and with $(\omega_{21},\omega_{22})$ for `false` at every key of `liveJointKeys` of the first global retained source (radius $Y=Z^{2L_{\mathrm{cap}}+15\eta+\tau}$, cutoff `firstDyadicRadius`, test $W(y)=$`normTwistedSource ω θ (y/Z^r)`, `rowMajorant`, $Z^M$), then $Z^{-r-2\ell-V}$ times the `CanonicalRowCompletion.rowFamilyEnergy` of the marked `varyingReopenedRow` rows at $Z^M$ is at most
--   $$C_{\mathrm{zero}}\Gamma^2Z^{M-\ell+3\eta+\varepsilon_{\mathrm{First}}(5\ell+2r+7\eta)}+C\Gamma^2(1+A)Z^{r+3\ell+V+\mathrm{loss}}(1+|\theta|)^{2k}Z^{(2L_{\mathrm{cap}}+15\eta+\tau)\varepsilon_{\mathrm{First}}+\varepsilon_{\mathrm{First}}}+C_{\mathrm{tail}}\Gamma^2Z^{-\mathrm{saving}},$$
--   $k=$`momentOrder (firstDegree degree)`.
--
--   Lean: `OAI.SevenEighths.InverseMoment.original_two_pass_energy` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstTwoPassEnergy.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform InverseMomentFirstLabelCell
open InverseMomentFirstSecondHeightCost
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_two_pass_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b)
    (Lcap eta tau saving em ed:ℝ)(hcap:0≤Lcap)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1)
    (hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁₁ ω₁₂ ω₂₁ ω₂₂:𝓢(ℝ,ℂ))(af₁ bf₁ af₂ bf₂ window bw:ℝ),
      0<af₁ ∧ af₁≤bf₁ ∧ 0<af₂ ∧ af₂≤bf₂ ∧
      HasCompactSupport (ω₁₁:ℝ→ℂ) ∧ HasCompactSupport (ω₁₂:ℝ→ℂ) ∧
      HasCompactSupport (ω₂₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂₂:ℝ→ℂ) ∧
      tsupport (ω₁₁:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧ tsupport (ω₁₂:ℝ→ℂ)⊆Set.Icc af₁ bf₁ ∧
      tsupport (ω₂₁:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧ tsupport (ω₂₂:ℝ→ℂ)⊆Set.Icc af₂ bf₂ ∧
      1≤bw ∧ b≤bw ∧ bw=Real.exp window ∧
    ∀epsFirst epsSecond:ℝ,0<epsFirst→0<epsSecond→∀degree:ℕ,
      ∃C Czero Ctail:ℝ,0≤C ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta pi epschild A loss:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Lcap)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤ r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hVcap:V≤Lcap)(_hwin:Real.exp window≤Z^eta)(_hpi:0≤pi)(_hpieta:6*eta≤pi)
      (_hemcost:em*(20*(3*Lcap+16)+30)≤pi/4)(_hedcost:ed*(20*(3*Lcap+16)+30)≤pi/4)
      (_hechild:0≤epschild)(_hsave: -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+epsSecond)
      (_hloss:48*eta+tau+pi+epschild+epsSecond≤loss)(_hcard:slots.card≤K)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hA:0≤A)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights ω₁₁ ω₁₂
        Z M r ell V eta tau window bw epschild A K degree)→
      (∀k∈keys,ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights ω₂₁ ω₂₂
        Z M r ell V eta tau window bw epschild A K degree)→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*Γ^2*Z^(M-ell+3*eta+epsFirst*(5*ell+2*r+7*eta))+
        C*Γ^2*(1+A)*Z^(r+3*ell+V+loss)*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder (firstDegree degree))*
          Z^((2*Lcap+15*eta+tau)*epsFirst+epsFirst)+Ctail*Γ^2*Z^(-saving) := by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
