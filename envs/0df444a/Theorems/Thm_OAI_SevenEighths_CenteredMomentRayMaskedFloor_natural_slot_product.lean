-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentRayMaskedFloor_natural_slot_product
-- name    : OAI.SevenEighths.CenteredMomentRayMaskedFloor.natural_slot_product
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:17:02.312518+00:00
-- url     : https://prove2.me/theorems/cc3f704e-f2f9-431d-ae2e-4c168aa7bd1d
-- title:
--   Products of natural prime slots are small
-- statement:
--   Let $M\ne0$ be an ideal of $\mathcal O$, $H$ a subgroup of $(\mathcal O/M)^\times$ containing `globalUnits M`, $F$ a finite index set, $W$ smooth with support in $[a,b]$, $a>0$, reals $L_{\mathrm{mod}},L_{\mathrm{slot}}\ge0$, `loss` $>0$, $lo,hi$ and $\kappa\ge2\beta-1$ with $\beta=$`beta` $\ge51/100$. Then there are a degree and $C>0$ such that for every `Character` $\eta_0$, for all sufficiently large $Z$: for all ray characters $\theta_i$, weights $0\le w_i\le L_{\mathrm{slot}}$, $\sigma_i\in[lo,hi]$, $|v_i|\le T$ ($T\ge0$) on $F$, $t$, every `Character` $\eta$, $z\ne0$, `NaturalRow` $N$ for $\eta,z$ with character modulus norm $\le Z^{L_{\mathrm{mod}}}$, every $Q\le M$ such that `FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z` fails, and every $A\subseteq F$:
--   $$\Big\|\prod_{i\in A}\texttt{naturalSlot}\,N.\mathrm{character}\,(\texttt{primePool}\,M\,H\,b\,Z^{w_i})\,(\texttt{heightCoefficient}(\dots)\,t)\,Z^{w_i}\Big\|^2\le C(1+|t|+T)^{\mathrm{degree}}Z^{\mathrm{loss}+\kappa\sum_{i\in F}w_i},$$
--   the coefficients being `idealCoeff (relativeCharacter M H hH η₀ (θ i))`·`annularWeight W (Z^{w_i}) (σ i) (v i)`.
--
--   Lean: `OAI.SevenEighths.CenteredMomentRayMaskedFloor.natural_slot_product` in `lean/OAI/NumberTheory/DirichletL/Moments/RayMaskedFloorSlots.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B022
import Definitions.Def_OAIHecke78B023

section

namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentPrimeSlot CenteredExceptionalProfile
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

attribute [local instance] OAI.SevenEighths.CenteredMomentRayMaskedFloor.instFiniteQuotientOIdeal
theorem natural_slot_product {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(z : O),z≠0 → ∀N : NaturalRow η z,
      (N.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
    ∀A : Finset α,A⊆F →
      ‖∏i∈A,naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      C*(1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  sorry

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end
