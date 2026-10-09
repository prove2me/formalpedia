-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyOriginalHighReflectionSymmetricBounded_original_unbalanced_from_low
-- name    : OAI.SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded.original_unbalanced_from_low
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:25:56.184981+00:00
-- url     : https://prove2.me/theorems/0da76f21-96af-4c27-ab0b-1800d9d52643
-- title:
--   Unbalanced energies from the positive low-length bound
-- statement:
--   Let $M,H,\alpha,W_{\mathrm{slot}}$ be as in the high-from-low statement and reals $lo,hi$, $0<a\le1/4$, $b\ge1$, $b_\Phi>0$, $\rho>0$, $\varepsilon>0$, $M_{\mathrm{cap}},B_{\mathrm{mask}}\ge0$. Then there are $d>0$, $0<\xi\le\rho/100$ and $L$ with $M_{\mathrm{cap}}+B_{\mathrm{mask}}+\xi\le L\le M_{\mathrm{cap}}+B_{\mathrm{mask}}+\rho/100$ such that for every degree and finite $S$ there are $J$, a finite $U$ and $C>0$ with: for all sufficiently large $Z$ ($Z>1$), whenever `PositiveLowAt … Mcap e κ Z η₀ Q degree S K` holds ($e,K\ge0$), for slot data as before, $\kappa\ge3/4$, every `NaturalState` $s$ with fixed modulus `internalQ Q η₀` and $\rho\le\mathrm{width}\le M_{\mathrm{cap}}$, Schwartz $W_1,W_2$ supported in $[a,b]$ and $X_1,X_2>0$ with $\min(\ell_1,\ell_2)\le\mathrm{width}/4$, $\tfrac56\mathrm{width}\le\ell_1+\ell_2+\sum w_i$ and $\ell_1+\ell_2+6\kappa\sum w_i\le\mathrm{width}$ ($\ell_k=$`length Z X_k`): the `energy` of $s$ is at most $C(K+1)\,\texttt{diagonalControl}\,(\texttt{sourceControl}\,U\,W_1\cdot\texttt{sourceControl}\,U\,W_2)^2(1+|t|+\mathrm{height})^JZ^{\mathrm{width}+e+\varepsilon}$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded.original_unbalanced_from_low` in `lean/OAI/NumberTheory/DirichletL/Energy/OriginalHighReflectionSymmetricBounded.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyBands CenteredMomentInductionEnergy
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyOriginalHighReflectionBounded
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskEnergy CenteredMomentCommonMaskExpansion
open CenteredMomentFiniteProfileExceptional QuadraticInitialBound CenteredMomentPrimeSlot
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

open CenteredMomentEnergyOriginalHighReflectionSymmetric

variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded.instFiniteQuotientOIdeal
theorem original_unbalanced_from_low
    (Wslot:ℝ→ℂ)(aslot bslot lo hi:ℝ)
    (haslot:0<aslot)(hsSlot:Function.support Wslot⊆Set.Icc aslot bslot)(hcSlot:Continuous Wslot)
    (a b bΦ rho ε Mcap Bmask:ℝ)
    (ha:0<a)(hlo:a≤1/4)(hhi:1≤b)(hbΦ:0<bΦ)(hrho:0< rho)(hε:0<ε)
    (hM:0≤Mcap)(hBmask:0≤Bmask):
    ∃d xi L:ℝ,0<d ∧ 0<xi ∧ xi≤ rho/100 ∧ Mcap+Bmask+xi≤L ∧ L≤Mcap+Bmask+rho/100 ∧
    ∀degree:ℕ,∀S:Finset (ℕ×ℕ),
    ∃J:ℕ,∃U:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(e Lslot κ:ℝ)(η₀:Character)(Q:Ideal O)(K:ℝ),0≤e → 0≤K →
      PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
        Mcap e κ Z η₀ Q degree S K →
      ∀(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤height → (∀i,|freq i|≤height) → 3/4≤κ →
      ∀(s:NaturalState Z Bmask bΦ),s.fixedModulus=internalQ Q η₀ → rho≤ s.width → s.width≤Mcap →
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b →
      ∀X₁ X₂:ℝ,0<X₁ → 0<X₂ →
      min (length Z X₁) (length Z X₂)≤ s.width/4 →
      5*s.width/6≤length Z X₁+length Z X₂+(∑i,w i) →
      length Z X₁+length Z X₂+6*κ*(∑i,w i)≤ s.width →
      energy s.character s.mask 1 t W₁ W₂
        (fun i=>primePool M H bslot (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I)
        (fun i=>Z^(w i)) X₁ X₂
        s.radial.keep s.radial.profile s.radial.scale ≤
      C*(K+1)*diagonalControl s.radial.profile*(sourceControl U W₁*sourceControl U W₂)^2*
        (1+|t|+height)^J*Z^(s.width+e+ε) := by
  sorry

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionSymmetricBounded

end

end OAI
end
