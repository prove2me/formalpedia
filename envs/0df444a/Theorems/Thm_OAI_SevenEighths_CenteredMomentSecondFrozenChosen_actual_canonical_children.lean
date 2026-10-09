-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondFrozenChosen_actual_canonical_children
-- name    : OAI.SevenEighths.CenteredMomentSecondFrozenChosen.actual_canonical_children
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:25.709264+00:00
-- url     : https://prove2.me/theorems/58aabe5a-8348-49e6-933d-1fdfe859d75e
-- title:
--   Nonexceptional physical blocks bounded by canonical child energies
-- statement:
--   For $\iota$ finite, $lo,hi$, Schwartz $W$, `decay`, $J_1,J_2$, $B\ge0$, $\delta>0$, there are $C_0,C_e>0$ such that eventually in $Z$, for every $K_{\mathrm{phys}}>0$, dyadic $n$ (ratio $r$), input $s$ with bounds $lo,hi$, character family $\tau$, $R_0$, `seed` and the hypotheses of the Lean (child energies at the canonical radials bounded by $E_1(1+|v|)^{2J_1}$ and $E_2(1+|v|)^{2J_2}$), the physical block over the nonexceptional rows `partRows false …` satisfies
--   $$\frac{\|\texttt{physicalBlock}\cdots\|}{\texttt{volume}\,s}\le\frac{C_0C_eZ^{2\delta}\,\texttt{profileCost}\,s\cdot\texttt{outerScalar}\cdot\texttt{normalizer}}{\sqrt{N(C)N(D)}}\sqrt{E_1E_2}\,\texttt{heightEnvelope}(s.t)^{J_1+J_2}\,\texttt{profileMoment}\,J_1\,\texttt{profileMoment}\,J_2/(1+r)^{\mathrm{decay}}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentSecondFrozenChosen.actual_canonical_children` in `lean/OAI/NumberTheory/DirichletL/Moments/SecondFrozenChosen.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSecondFrozenChosen
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT
open CenteredMomentSecondSectorColumns CenteredMomentSecondCanonical CenteredMomentCanonicalFirst
open CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit CenteredMomentSecondCanonicalScalar
open CenteredMomentLogDyadic CenteredMomentSmooth CenteredMomentSupport
open CenteredMomentRestrictedEnergy CenteredMomentSecondScaled
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentRowNorm
open CenteredMomentHeckeColumnWindow CenteredMomentSectorLocalization RayFourExpansion
open CenteredMomentSecondWindowBudget
open CenteredMomentRestrictedSource CenteredMomentFirstSectors
open CenteredMomentSecondNonexceptionalChosenBlock CenteredMomentSourceLiveColumn
local notation "O" => ActualEisensteinCubic.O

open Filter
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonRadialData CenteredMomentCommonRadialPointwise
open CenteredMomentRadialEligibleEnergy CenteredMomentSourceMass CenteredMomentSourceProfileMass
open CenteredMomentCommonAllocationSum CenteredMomentEligibleEnergy
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentSecondOriginalChildren
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonicalScalar
open CenteredMomentSecondWholeKernel
open CenteredMomentCommonRadialData CenteredMomentExceptionalAmplitudePair

open CenteredMomentSecondHeightFamily
open CenteredMomentSecondExceptionalFamily CenteredMomentSecondEnergySplit
open CenteredMomentSecondDyadicRowSupport CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalCommonHarmonic CenteredMomentExceptionalAmplitudePair

attribute [local instance] OAI.SevenEighths.CenteredMomentSecondFrozenChosen.instDecidableEqSumFinOfNatNat_solutions
theorem actual_canonical_children (lo hi:ι→ℝ) (W : 𝓢(ℝ,ℂ)) (decay J₁ J₂ : ℕ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0 Ce:ℝ,0<C0 ∧ 0<Ce ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Kphys:ℝ,0<Kphys → ∀n:Fin 4→ℤ,
      let r:=dyadicScale (n 0)*dyadicScale (n 1)/(dyadicScale (n 2)*dyadicScale (n 3))
      ;
      ∀(s:Input ι) (τ:RayCharacter→Character),
      (∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) → ∀R0 seed:Ideal O,
      let S:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R0 s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      ∀(C D:Ideal O) (hC:Supported C) (hD:Supported D),
      seed∣C → seed∣D → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm D:ℝ)≤Z^B →
      primeSupport C=primeSupport D → ∀U:Finset (CommonIndex C D),
      let _A:=commonFrequencyGenerator C D*nonunitFrequencyGenerator C D U
      Family s.η C D hC hD U τ →
      s.W₁ 0=0 → s.W₂ 0=0 → sourceRadius s≤Z^B →
      ∀R:ℝ,
      ∀(Q:Ideal O) (m:O) (χ₀:RayCharacter),Q≤Ideal.span {(72:O)} →
      m≠0 → ConcretePrimeRowBridge.goodLambda∣m → (2:O)∣m →
      ∀E₁ E₂:ℝ,
      0≤E₁ → 0≤E₂ →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools C,
        frozenCoefficient b.val C R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) C R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) C R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₁*(1+‖v‖)^(2*J₁)) →
      (∀L∈divisorPool Finset.univ (fun J:sectorPool D hD.1 S=>(J:Ideal O)),(L.absNorm:ℝ)≤ sourceRadius s/(D.absNorm:ℝ) → Squarefree L →
        ∀χ:RayCharacter,∀v:ℝ,∀b:actualAllocations s.pools D,
        frozenCoefficient b.val D R0 s.ν s.W s.P≠0 →
        ∀a∈(commonData (withHeight s (τ χ) v) D R0 b).toSource.active L,
          childEnergy (commonData (withHeight s (τ χ) v) D R0 b)
            (canonicalRadial (τ χ) Q n) L a≤E₂*(1+‖v‖)^(2*J₂)) →
      ‖physicalBlock s.η s.t S β C D hC hD U R
        (partRows false s.η χ₀ Q m C D U R) W Kphys n‖/volume s.toData≤
        (C0*Ce)*Z^(2*δ)*profileCost s*(outerScalar C D Kphys n*normalizer C D U)/
          Real.sqrt ((C.absNorm:ℝ)*D.absNorm)*Real.sqrt (E₁*E₂)*
          heightEnvelope s.t^(J₁+J₂)*profileMoment J₁*profileMoment J₂/(1+r)^decay := by
  sorry

end SevenEighths.CenteredMomentSecondFrozenChosen

end

end OAI
end
