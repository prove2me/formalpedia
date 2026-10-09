-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_original_dyadic_retained_budget
-- name    : OAI.SevenEighths.InverseMoment.original_dyadic_retained_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:58:11.974011+00:00
-- url     : https://prove2.me/theorems/6d3c5d3a-50b1-4e6f-beb9-2f91850e30f5
-- title:
--   Retained family bounded by refined child energies
-- statement:
--   Let $\omega,\Phi$ be Schwartz with $\omega$ supported in $[a,b]$, $a>0$, $b\ge0$, and $L_{\mathrm{cap}}\ge0$. Then there are compactly supported Schwartz $\omega_1,\omega_2$ with support in $[lo,hi]$, $0<lo\le hi$, such that for every $\varepsilon>0$ and $J$ there is $C\ge0$ such that for every family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` (residue characteristic $\ne2$, `goodLambda`$^2\mid p_i-1$), `pool`, finite $Q$ with cube primary products $\le Z^{\ell+\eta}$, squarefree nonzero `labels`, coefficients $\beta$ bounded by $\Gamma\ge0$, $\Psi$ bounded by 1, $m$, `mark`, and reals $Z\ge2$, $Z^\eta\ge2$, $M\ge0$, $r,\ell\le L_{\mathrm{cap}}$, $0\le F_{\max}\le L_{\mathrm{cap}}$ with $r+3\ell+V\le F_{\max}$, $0\le\eta,\tau\le1$, $K>0$, $\theta$, $B_{\mathrm{energy}}\ge0$: writing $Y=Z^{2F_{\max}+15\eta+\tau}$, the cutoff `firstDyadicRadius`, $W(y)=$`normTwistedSource ω θ (y/Z^r)`, the first global retained source and its `liveJointKeys`, if for every key $k$ and frequency $z$ both scaled `refinedChildEnergy` values (left with $\omega_1$ at coordinate 7, right with $\omega_2$ at coordinate 8) are at most $B_{\mathrm{energy}}\cdot$`tripleHeight J z.1`$\cdot$`coordinateHeight J z.2`, then
--   $$Z^{-r-2\ell-V}Z^M\,\|\texttt{originalRetainedFamily}(\dots,W,\Phi,K,Y,\mathrm{cutoff},1)\|\le C\,\Gamma^2B_{\mathrm{energy}}(1+|\theta|)^{2k}Z^{(2F_{\max}+15\eta+\tau)\varepsilon+\varepsilon},$$
--   $k=$`momentOrder J`.
--
--   Lean: `OAI.SevenEighths.InverseMoment.original_dyadic_retained_budget` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstDyadicRetainedBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B019

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_retained_budget
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap:ℝ)(hcap:0≤Lcap)(hb:0≤b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤C ∧
    ∀{ι:Type}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Fmax)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)(_hF0:0≤Fmax)(_hFcap:Fmax≤Lcap)
      (_heta:0≤eta)(_heta1:eta≤1)(_htau:0≤tau)(_htau1:tau≤1)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) true Ψ m mark omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) false Ψ m mark omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps+eps) := by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
