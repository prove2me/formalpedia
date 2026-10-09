-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroGrowthReflection_live_deleted_reflection
-- name    : OAI.SevenEighths.CenteredMomentEnergyZeroGrowthReflection.live_deleted_reflection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:29.831876+00:00
-- url     : https://prove2.me/theorems/5f60447b-288d-43b0-8812-d2fc50f0e3f3
-- title:
--   Live deleted energies by reflection under zero growth
-- statement:
--   For $0<a\le1/4$, $b\ge1$, $b_\Phi,\epsilon,\xi,\mathrm{defect}>0$, `saving`, $L_{\mathrm{reflect}}$, $B\ge2$ and a finite $S$, there are $n$, $T$, $D_{\mathrm{child}}>0$, $n_{\mathrm{long}}$, $S_{\mathrm{long}}$, $C,D>0$ such that, eventually in $Z$, under `ZeroGrowthAt` (constant $K\ge0$) and the hypotheses of the Lean, the `radialEnergy` of the deleted long-times-short polynomials is at most $C\max(\dots)^{\epsilon}(\texttt{sourceControl}\,S_{\mathrm{long}}\,W_{\mathrm{long}})^2(1+|t|)^{2n_{\mathrm{long}}}(1+2\max(0,\mathrm{width}-\mathrm{along}+\xi)\log Z)E+D\max(\dots)^{2\epsilon}(\dots)^2(1+|t|)^{2n_{\mathrm{long}}}Z^{-2\,\mathrm{saving}}\texttt{radialEnergy}(\text{short polynomial at }X_{\mathrm{short}}/N_s)$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyZeroGrowthReflection.live_deleted_reflection` in `lean/OAI/NumberTheory/DirichletL/Energy/ZeroGrowthReflection.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025
import Definitions.Def_OAIHecke78B028

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroGrowthReflection
open CenteredMomentNaturalRowSource
open HeckeFamily HeckeDyadic QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentEnergyZeroGrowth
open CenteredMomentEnergyZeroReflectionSupport
open CenteredMomentEnergyReferenceState
open CenteredMomentFiniteProfileExceptional
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
local notation "O"=>HeckeFamily.O

theorem live_deleted_reflection (a b bΦ epsilon xi defect saving Lreflect:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)
    (hepsilon:0<epsilon)(hxi:0<xi)(hdefect:0<defect)
    (B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D:ℝ,0<C ∧ 0<D ∧
    ∀ᶠZ:ℝ in atTop,1<Z ∧
    ∀(Bmask L Mcap loss:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K→
    ZeroGrowthAt Q a b bΦ Bmask L Mcap loss Z degree S K→0≤Bmask→
    Mcap+Bmask+defect+xi≤L→Mcap+Bmask+defect≤Lreflect→
    ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤Mcap→
    ∀Wlong Wshort:𝓢(ℝ,ℂ),Function.support (Wlong:ℝ→ℂ)⊆Set.Icc a b→
    Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b→
    ∀t Xshort Xlong:ℝ,0<Xshort→Xshort≤Xlong→Xshort≤Z^L→1≤b*Xlong→
    ∀Dshort Dlong:Finset (Ideal O),
    Dshort∈(CompletedGauss.primeSupport s.puncture).powerset→
    Dlong∈(CompletedGauss.primeSupport s.puncture).powerset→
    let Ns:ℝ:=(∏P∈Dshort,P).absNorm;
    let Nl:ℝ:=(∏P∈Dlong,P).absNorm;
    let along:=Real.logb Z (Xlong/Nl);
    0≤ s.width-along+xi→
    let E:=K*diagonalControl s.radial.profile*Dchild*(sourceControl T Wshort)^2*
      (1+|t|)^(2*n)*Z^(s.width+loss+defect+xi)*Nl;
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wlong (Xlong/Nl) 0 t*
      polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*
        (1+2*(max 0 (s.width-along+xi)*Real.log Z))*E+
      D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
        (sourceControl Slong Wlong)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
        radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false Wshort (Xshort/Ns) 0 t)
          (effectiveState s).radial.keep s.radial.profile s.radial.scale:= by
  sorry
end SevenEighths.CenteredMomentEnergyZeroGrowthReflection

end

end OAI
end
