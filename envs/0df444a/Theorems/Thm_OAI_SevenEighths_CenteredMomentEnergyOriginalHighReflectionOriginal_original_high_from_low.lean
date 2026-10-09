-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyOriginalHighReflectionOriginal_original_high_from_low
-- name    : OAI.SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal.original_high_from_low
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:27:46.724376+00:00
-- url     : https://prove2.me/theorems/88582bd8-4e45-4c7b-9cf9-150023ab92a1
-- title:
--   High-length energies from the positive low-length bound
-- statement:
--   Let $M\ne0$, $H\supseteq$`globalUnits M`, $\alpha$ finite, $\varepsilon_{\mathrm{Delete}}>0$, $W_{\mathrm{slot}}$ continuous with support in $[a_{\mathrm{slot}},b_{\mathrm{slot}}]$ ($a_{\mathrm{slot}}>0$), and reals $lo,hi$, $0<a\le1/4$, $b\ge1$, $b_\Phi>0$, $\epsilon>0$, $\xi>0$, `saving`, $M_{\mathrm{cap}}$, $B_{\mathrm{mask}}\ge0$, $L\ge M_{\mathrm{cap}}+B_{\mathrm{mask}}+\xi$, $B\ge2$, a degree and a finite $S$. Then there are $n$, a finite $T$, $D_{\mathrm{child}}>0$, $n_{\mathrm{long}}$, a finite $S_{\mathrm{long}}$ and $C,D,C_{\mathrm{weight}}>0$ such that for all sufficiently large $Z$ ($Z>1$): whenever `PositiveLowAt … Z η₀ Q degree S K` holds ($K\ge0$), for all ray characters $\theta_i$, weights $0\le w_i\le L_{\mathrm{slot}}$, $\sigma_i\in[lo,hi]$, $|\mathrm{freq}_i|\le\mathrm{height}$, $t$, $\kappa\ge3/4$, every `NaturalState` $s$ with fixed modulus `internalQ Q η₀`, width $\le M_{\mathrm{cap}}$ and $\xi\le\mathrm{width}/14$, Schwartz $W_1,W_2$ supported in $[a,b]$, and $X_1,X_2>0$ with `length Z X₁` $\le\mathrm{width}/4$ and $\tfrac56\mathrm{width}\le\ell_1+\ell_2+\sum w_i$, $\ell_1+\ell_2+6\kappa\sum w_i\le\mathrm{width}$: the `energy` of $s$ with the prime-slot pools and coefficients is at most $C_{\mathrm{weight}}N(\operatorname{rad}s.\mathrm{puncture})^{\varepsilon_{\mathrm{Delete}}}$ times the sum of three terms listed in the Lean — a positive-low term $K\cdot$`diagonalControl`$\cdot$(independent profile control)$^2(1+|t|+\mathrm{height})^{\mathrm{degree}}Z^{\mathrm{width}+\varepsilon}$, a long-reflection term involving `sourceControl Slong W₂`, `sourceControl T W₁`, $D_{\mathrm{child}}$ and $(1+2L\log Z)$, and a remainder of size $D\cdot\dots\cdot Z^{-2\,\mathrm{saving}}$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal.original_high_from_low` in `lean/OAI/NumberTheory/DirichletL/Energy/OriginalHighReflectionOriginal.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyReferenceLowReflectionError
open CenteredMomentEnergyReferenceLowDirect CenteredMomentEnergyReferenceChild
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentOriginalRadialComparison CenteredMomentAllocatedNaturalRadial
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

open CenteredMomentEnergyOriginalHighReflectionDeleted
open CenteredMomentInductionEnergy
attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal.instFiniteQuotientOIdeal
theorem original_high_from_low
    (epsilonDelete:ℝ)(hepsilonDelete:0<epsilonDelete)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ epsilon xi saving Mcap Bmask L:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hepsilon:0<epsilon)(hxi:0<xi)
    (hBmask:0≤Bmask)(hL:Mcap+Bmask+xi≤L)
    (B:ℕ)(hB:2≤B)(degree:ℕ)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃Dchild:ℝ,0<Dchild ∧
    ∃nlong:ℕ,∃Slong:Finset (ℕ×ℕ),∃C D Cweight:ℝ,0<C ∧ 0<D ∧ 0<Cweight ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(Lslot ε κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap ε κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → s.width≤Mcap → xi≤ s.width/14 →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      length Z X₁≤ s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      Cweight*(s.puncture.radical.absNorm:ℝ)^epsilonDelete*(
        K*diagonalControl s.radial.profile*
          ((independentProfiles ha W₁ W₂ hs₁ hs₂ t t).control S)^2*
          (1+|t|+height)^degree*Z^(s.width+ε) +
        (C*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^epsilon *
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*
          (1+2*(L*Real.log Z))*
          (K*diagonalControl s.radial.profile*Dchild*(sourceControl T W₁)^2*
            (1+|t|+height)^(degree+2*n)*Z^(s.width+ε)) +
        D*(max 1 ((fixedConductorFactor:ℝ)*bΦ*Z^s.width))^(2*epsilon)*
          (sourceControl Slong W₂)^2*(1+‖t‖)^(2*nlong)*Z^(-2*saving)*
          ((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W₁)^2*
            diagonalControl s.radial.profile*max 1 s.radial.scale*(Z^(s.width/4))*∏i,Z^(w i))) := by
  sorry

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionOriginal

end

end OAI
end
