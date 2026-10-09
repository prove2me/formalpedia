-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCapacityRemoval_actual_state_capacity_removal
-- name    : OAI.SevenEighths.CenteredMomentEnergyCapacityRemoval.actual_state_capacity_removal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:16:31.09708+00:00
-- url     : https://prove2.me/theorems/e3f922d5-d4a4-4f40-b683-35e441dd70e4
-- title:
--   Removing slots beyond the live capacity
-- statement:
--   Let $M\ne0$ be an ideal of $\mathcal O$ (`HeckeFamily.O`), $H$ a subgroup of $(\mathcal O/M)^\times$ containing `globalUnits M`, $\iota$ finite, $W_i$ smooth with support in $[a_i,b_i]$, $a_i>0$, reals $M_{\mathrm{row}}$, $b_\Phi\ge0$, $L_{\mathrm{mod}},L_{\mathrm{slot}}\ge0$, $\varepsilon>0$, $lo,hi$ and $\kappa\ge2\beta-1$ with $\beta=$`HeckeZeroSupremum.beta` $\ge51/100$. Then there are a degree and $C>0$ such that for every family of characters $\nu_i$ there is $Z_0>1$ with: for every finite $J$, weights $0\le w_i\le\min(\mathrm{mesh},L_{\mathrm{slot}})$ and reals $n_1,n_2$, `width`, $\mathrm{mesh}\ge0$, there is $R\subseteq J$ with $R=J$ or $n_1+n_2+6\kappa\sum_{J\setminus R}w_i\le\mathrm{width}$, and $\kappa\sum_Rw_i\le$`excess J w n₁ n₂ width κ`$/6+\kappa\,\mathrm{mesh}$, such that for all $Z\ge Z_0$, every `NaturalState` $s$ with trivial puncture, row width $\le M_{\mathrm{row}}$, character modulus norm $\le Z^q$ with $M_{\mathrm{row}}+q+1\le L_{\mathrm{mod}}$, fixed modulus $Q\le M$ and $Q\le\nu_i.\mathrm{modulus}$, all $\sigma_i\in[lo,hi]$, $|\mathrm{freq}_i|\le V$, $t$, $X_1,X_2>0$: the `energy` with all slots of $J$ (prime pools `primePool M H (b i) (Z^{w_i})`, coefficients `idealCoeff (ν i)`·`annularWeight`) is at most
--   $$C(1+|t|+V)^{\mathrm{degree}}Z^{\varepsilon+\texttt{excess}/6+\kappa\,\mathrm{mesh}}\cdot(\text{the same energy with the slots of }J\setminus R).$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyCapacityRemoval.actual_state_capacity_removal` in `lean/OAI/NumberTheory/DirichletL/Energy/CapacityRemoval.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B024

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCapacityRemoval
open HeckeFamily ConcreteTraceCRT CenteredMomentRetainedEnergy
open CenteredMomentInductionEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentSecondHeightFamily CenteredMomentEnergyState
open CenteredExceptionalProfile CenteredMomentFixedRowMask
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (M : Ideal O) [NeZero M]
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
include hH

attribute [local instance] OAI.SevenEighths.CenteredMomentEnergyCapacityRemoval.instFiniteQuotientOIdeal
theorem actual_state_capacity_removal
    (W : ι→ℝ→ℂ) (a b : ι→ℝ) (ha : ∀i,0<a i)
    (hWs : ∀i,Function.support (W i)⊆Set.Icc (a i) (b i))
    (hW : ∀i,ContDiff ℝ ∞ (W i))
    (Mrow bΦ Lmod Lslot ε lo hi κ : ℝ) (hbΦ : 0≤bΦ)
    (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hε : 0<ε)
    (hbeta : (51/100:ℝ)≤HeckeZeroSupremum.beta) (hκ : 2*HeckeZeroSupremum.beta-1≤κ) :
    ∃degree:ℕ,∃C:ℝ,0<C ∧ ∀ν:ι→Character,∃Z₀:ℝ,1<Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤ mesh →
      (∀i,0≤w i) → (∀i,w i≤ mesh) → (∀i,w i≤Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤width) ∧
      κ*(∑i∈R,w i)≤CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤Z → ∀Bmask:ℝ,∀s:NaturalState Z Bmask bΦ,
      s.puncture=1 → s.rowWidth≤Mrow → ∀q:ℝ,
      (s.character.modulus.absNorm:ℝ)≤Z^q → Mrow+q+1≤Lmod →
    ∀Q:Ideal O,s.fixedModulus=Q → Q≤M → (∀i,Q≤(ν i).modulus) →
    ∀(σ freq:ι→ℝ)(t V:ℝ),(∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|freq i|≤V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),0<X₁ → 0<X₂ →
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I
      energy s.character s.mask 1 t W₁ W₂ (fun i:J=>S i) (fun i:J=>coeff i)
        (fun i:J=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          energy s.character s.mask 1 t W₁ W₂ (fun i:↥(J\R)=>S i) (fun i:↥(J\R)=>coeff i)
            (fun i:↥(J\R)=>P i) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale := by
  sorry

end SevenEighths.CenteredMomentEnergyCapacityRemoval

end

end OAI
end
