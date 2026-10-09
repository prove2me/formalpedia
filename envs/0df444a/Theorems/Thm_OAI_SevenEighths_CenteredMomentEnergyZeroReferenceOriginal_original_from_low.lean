-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyZeroReferenceOriginal_original_from_low
-- name    : OAI.SevenEighths.CenteredMomentEnergyZeroReferenceOriginal.original_from_low
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:26:17.888169+00:00
-- url     : https://prove2.me/theorems/97ad4ad0-925e-437c-a9d3-e0bc9239fe3b
-- title:
--   Zero-stage plain energy at the comparison lengths from the low bound
-- statement:
--   For $\varepsilon_{\mathrm{Delete}}>0$, reals $0<a\le1/4$, $b\ge1$, $b_\Phi>0$, $\epsilon>0$, $\xi>0$, `saving`, $M_{\mathrm{cap}}$, $B_{\mathrm{mask}}\ge0$, $L\ge M_{\mathrm{cap}}+B_{\mathrm{mask}}+\xi$, $B\ge2$ and a finite $S$, there are $n$, $T$, $D_{\mathrm{child}}>0$, $n_{\mathrm{long}}$, $S_{\mathrm{long}}$, $C,D,C_{\mathrm{weight}}>0$ such that for all sufficiently large $Z$: whenever `ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K` holds ($K\ge0$), for every `NaturalState` $s$ with fixed modulus $Q$, width $\le M_{\mathrm{cap}}$ and $\xi\le\mathrm{width}/6$, every `Profiles a b` $p$, $t$ and $X_1,X_2>0$ with $\mathrm{width}/4\le\log_Z(X_1X_2)$: `s.plainEnergy p t (comparisonFirst …) (comparisonSecond …)` is at most $C_{\mathrm{weight}}N(\operatorname{rad}s.\mathrm{puncture})^{\varepsilon_{\mathrm{Delete}}}$ times the sum of a low term $K\,\texttt{diagonalControl}\,(\text{profile control})^2Z^{\mathrm{width}+\varepsilon}$, a long-reflection term with $D_{\mathrm{child}}$ and $(1+2L\log Z)$, and a $Z^{-2\,\mathrm{saving}}$ remainder, exactly as written in the Lean.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyZeroReferenceOriginal.original_from_low` in `lean/OAI/NumberTheory/DirichletL/Energy/ZeroReferenceOriginal.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroReferenceOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O

theorem original_from_low (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)(B:ℕ)(hB:2≤B)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(ε:ℝ)(Q:Ideal O)(degree:ℕ)(K:ℝ),0≤K →
      ZeroLowAt Q a b bΦ Bmask L Mcap ε Z degree S K →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=Q →s.width≤Mcap →xi≤ s.width/6 →
      ∀(p:Profiles a b)(t X₁ X₂:ℝ),0<X₁ →0<X₂ →s.width/4≤Real.logb Z (X₁*X₂) →
      s.plainEnergy p t (comparisonFirst Z s.width) (comparisonSecond Z s.width X₁ X₂) ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) t t).control S)^2*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T (p.profile 0))^2*
            (1+|t|)^(2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong (p.profile 1))^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) (p.profile 0))^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*Z^(s.width/4))):= by
  sorry

end SevenEighths.CenteredMomentEnergyZeroReferenceOriginal

end

end OAI
end
