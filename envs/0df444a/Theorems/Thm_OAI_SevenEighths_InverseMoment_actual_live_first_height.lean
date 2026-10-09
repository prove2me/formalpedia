-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_actual_live_first_height
-- name    : OAI.SevenEighths.InverseMoment.actual_live_first_height
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:26.554672+00:00
-- url     : https://prove2.me/theorems/14d09bc3-acc0-4d63-a734-7f6285d0ed8c
-- title:
--   First-height energy of live joint keys from child bounds
-- statement:
--   Let `old` vanish beyond `oldb`, $\omega$ Schwartz with support in $[lo,hi]$ ($lo>0$), `negative` Boolean, and reals $F\ge0$, $\tau>0$, `saving`, `window`, $b\ge1$, $e_m,e_d>0$ with $hi\le b\le e^{\mathrm{window}}$ and `oldb` $\le e^{\mathrm{window}}$, and $K\in\mathbb N$. Then there are compactly supported Schwartz $\omega_1,\omega_2$ with support in $[a_f,b_f]$, $0<a_f\le b_f$, such that for every `degree` and every $\mathrm{eps}>0$ there is $C>0$ with the following property. For every family $p$ of nonzero Eisenstein integers generating maximal, pairwise coprime, distinct ideals avoiding `goodLambda` (with `goodLambda`$^2\mid p_i-1$, residue characteristic $\ne2$), `pool`, finite $Q$, `labels` of nonzero ideals, $\beta$, $\Psi$ bounded by 1, $m$, at most $K$ slots with pairwise disjoint lists and weights bounded by 1, Schwartz $\Phi$, and reals satisfying the numerical constraints of the Lean (among them $Z\ge2$, $Z^\eta\ge2$, $0\le M,\ell,V\le F$, $-\eta\le r\le F$, $0\le\eta\le1$, $\tau\le1$, $e^{\mathrm{window}}\le Z^\eta$, $6\eta\le\pi$, $e_m(20(3F+16)+30)\le\pi/4$, the same for $e_d$, cube primary products $\le Z^{\ell+\eta}$, $A,\varepsilon_{\mathrm{child}}\ge0$, $-\mathrm{saving}\le r+3\ell+V+48\eta+\tau+\pi+\varepsilon_{\mathrm{child}}+\mathrm{eps}$ and $48\eta+\tau+\pi+\varepsilon_{\mathrm{child}}+\mathrm{eps}\le\mathrm{loss}$): for every key $k$ in `liveJointKeys` of the first global retained source (with cutoffs `firstDyadicRadius`, test `normTwistedSource old θ (·/Z^r)` and marks `primeMark`) for which `ChildBounds` holds, and every frequency $z$, the quantity $Z^{\texttt{firstKappa}(\dots)}e^{9\eta\log Z/2}\cdot$`globalPriorityOriginalEnergy`(…, `firstHeight negative z`, `firstCellRadius …`) is at most
--   $$C(1+A)Z^{r+3\ell+V+\mathrm{loss}}\cdot\texttt{tripleHeight}\,d'\,z_1\cdot\texttt{coordinateHeight}\,d'\,z_2,\qquad d'=\texttt{firstDegree}\ \mathrm{degree}.$$
--
--   Lean: `OAI.SevenEighths.InverseMoment.actual_live_first_height` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstLiveHeightStep.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open InverseAmbientProfileTower JointLogSeparation FourierBridge
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_live_first_height
    (old:ℝ → ℂ)(oldb:ℝ)(hsold:∀y,old y≠0 → y≤oldb)
    (om:𝓢(ℝ,ℂ))(lo hi:ℝ)(hlo:0<lo)(hs:Function.support om⊆Set.Icc lo hi)(negative:Bool)
    (F tau saving window b em ed:ℝ)(hF:0≤F)(htau:0<tau)(hb:1≤b)
    (hhib:hi≤b)(hwindow: b≤Real.exp window)(hold:oldb≤Real.exp window)(hem:0<em)(hed:0<ed)(K:ℕ):
    ∃(ω₁ ω₂:𝓢(ℝ,ℂ))(af bf:ℝ),0<af ∧ af≤bf ∧ HasCompactSupport (ω₁:ℝ → ℂ) ∧ HasCompactSupport (ω₂:ℝ → ℂ) ∧
      tsupport (ω₁:ℝ → ℂ)⊆Set.Icc af bf ∧ tsupport (ω₂:ℝ → ℂ)⊆Set.Icc af bf ∧
    ∀degree:ℕ,∀eps:ℝ,0<eps → ∃C:ℝ,0<C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι → O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι →₀ ℕ))(labels:Finset (Ideal O))(β:Ideal O → (ι →₀ ℕ) → ℂ)
      (Ψ:O →* ℂ)(m:O)(slots:Finset σ)(lists:σ → Finset ι)(weights:σ → ι → ℂ)
      (Φ:𝓢(ℝ,ℂ))(Z M r ell V eta pi epschild A theta Kphysical loss:ℝ),
      2≤Z → 2≤Z^eta → 0≤M → M≤F →  (-eta≤ r)  → r≤F → 0≤ell → ell≤F → 0≤V → V≤F →
      0≤eta → eta≤1 → tau≤1 → Real.exp window≤Z^eta → 0≤pi → 6*eta≤pi →
      em*(20*(3*F+16)+30)≤pi/4 → ed*(20*(3*F+16)+30)≤pi/4 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀u,‖Ψ u‖≤1) → (slots:Set σ).PairwiseDisjoint lists → slots.card≤K →
      (∀i∈slots,∀q∈lists i,‖weights i q‖≤1) → 0≤A → 0≤epschild → -saving≤ r+3*ell+V+48*eta+tau+pi+epschild+eps →
      48*eta+tau+pi+epschild+eps≤loss →
      let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource old theta (y/Z^r);
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
      ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ Kphysical),
      ChildBounds p hp hcop hg pool Q k.1 k.2.1 k.2.2 negative Ψ m slots lists weights ω₁ ω₂
        Z M r ell V eta tau window b epschild A K degree → ∀z:Frequency×(Fin 9 → ℝ),
      (Z^(firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4)))*
        Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      globalPriorityOriginalEnergy p hg hp hinj (extra negative) pool
        (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2) (parentWeight p k.2.1)
        negative Ψ m slots lists weights om (columnScale Z r k.1 k.2.1 negative) (InverseMomentFirstSecondHeightCost.firstHeight negative z) (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤
      (C*(1+A)*Z^(r+3*ell+V+loss))*
        (tripleHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.1*
          coordinateHeight (InverseMomentFirstSecondHeightCost.firstDegree degree) z.2) := by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
