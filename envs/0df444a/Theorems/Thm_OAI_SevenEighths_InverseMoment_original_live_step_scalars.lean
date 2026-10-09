-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_original_live_step_scalars
-- name    : OAI.SevenEighths.InverseMoment.original_live_step_scalars
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T01:51:45.002674+00:00
-- url     : https://prove2.me/theorems/a488df0e-3fe4-4422-b346-d674be23d4da
-- title:
--   Scalar bookkeeping for live joint keys
-- statement:
--   Let $p$ be a family of nonzero Eisenstein integers generating maximal, pairwise coprime ideals avoiding `goodLambda`; `pool`, $Q$ with cube primary products $\le Z^{\ell+\eta}$, nonzero `labels`, $\beta$, $\Psi$, $m$, `mark`, $\omega$ vanishing beyond `oldb`, Schwartz $\Phi$, and reals $K$, $Z>1$ with $Z^\eta\ge2$, $0\le M\le F$, $-\eta\le r\le F$, $0\le\ell\le F$, $0\le V\le F$, $0\le\eta\le1$, $0\le\tau\le1$, $\theta$, `oldb`, $b\le e^{\mathrm{window}}\le Z^\eta$ (with `oldb` $\le e^{\mathrm{window}}$), $e_m,e_d\ge0$, $\pi\ge6\eta$, $e_m(20(3F+16)+30)\le\pi/4$ and the same for $e_d$. Put $A=3F+16$. Then for every key $k$ of `liveJointKeys` of the first global retained source (cutoff `firstDyadicRadius`, $W(y)=$`normTwistedSource ω θ (y/Z^r)`, radius $Z^{2F+15\eta+\tau}$) and every Boolean `negative`, with $X=$`columnScale Z r k.1 k.2.1 negative` and $Y=$`firstCellRadius Z M r ℓ V η τ k.1 k.2.2`: $1\le Y\le Z^{16A+20}$, $Y^{-1}\le Z^{4A+2}$, $1\le Xe^{\mathrm{window}}\le Z^{A+1}$, $bX\le Z^{16A+20}$, and the further exponent inequalities listed in the Lean (on `exponent Z (k.1 i)`, `columnA`, `firstKappa`, and the two mass budgets bounded by $\pi$, respectively $\pi+\eta/2$) all hold.
--
--   Lean: `OAI.SevenEighths.InverseMoment.original_live_step_scalars` in `lean/OAI/NumberTheory/DirichletL/Descent/FirstLiveStepScalars.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open InverseMomentFirstOriginalProfile InverseMomentFirstLabelCell CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

 theorem original_live_step_scalars {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z M r ell V F eta tau theta oldb b window em ed pi:ℝ)
    (hZ:1<Z)(hbin:2≤Z^eta)(hF:0≤F)(hM:0≤M)(hMF:M≤F)
    (hr: -eta≤ r)(hrF:r≤F)(hell:0≤ell)(hellF:ell≤F)(hV:0≤V)(hVF:V≤F)
    (heta:0≤eta)(heta1:eta≤1)(htau:0≤tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤Z^eta)(hold:oldb≤Real.exp window)(hb:b≤Real.exp window)
    (hem:0≤em)(hed:0≤ed)(hpi:0≤pi)(hetapi:6*eta≤pi)
    (hsmall:em*(20*(3*F+16)+30)≤pi/4)(hsmall':ed*(20*(3*F+16)+30)≤pi/4)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤oldb):
    let A:=3*F+16;
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
    let W:=fun y=>normTwistedSource om theta (y/Z^r);
    let S:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) (Z^(2*F+15*eta+tau));
    ∀k∈liveJointKeys p S pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),∀negative:Bool,
      let X:=columnScale Z r k.1 k.2.1 negative;
      let Y:=firstCellRadius Z M r ell V eta tau k.1 k.2.2;
      1≤Y ∧ 1≤X*Real.exp window ∧ X*Real.exp window≤Z^(A+1) ∧ Y≤Z^(16*A+20) ∧ Y⁻¹≤Z^(4*A+2) ∧
      b*X≤Z^(16*A+20) ∧ exponent Z (k.1 3)+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
      firstKappa M r ell V (exponent Z (k.1 3)) (columnA Z k.1 negative) (exponent Z (k.1 2)) (exponent Z (k.1 4))+
        (9/2:ℝ)*eta≤16*A+20 ∧
      em*(ell+exponent Z (k.1 4)/2+exponent Z k.2.1+(16*A+20)+11*eta/2)≤pi ∧
      em*(r-columnA Z k.1 negative-exponent Z (k.1 2)-exponent Z k.2.1)+7*eta/2+
        ed*(3*ell+exponent Z (k.1 2)+exponent Z k.2.1+5*eta)+
        2*em*(2*ell+exponent Z (k.1 2)+exponent Z k.2.1+4*eta)≤pi+eta/2 ∧
      ell+eta≤16*A+20 ∧ exponent Z (k.1 4)+eta≤16*A+20 ∧
      exponent Z (k.1 2)+eta≤16*A+20 ∧ exponent Z k.2.1+eta≤16*A+20:= by
  sorry

end SevenEighths.InverseMoment

end

end OAI
end
