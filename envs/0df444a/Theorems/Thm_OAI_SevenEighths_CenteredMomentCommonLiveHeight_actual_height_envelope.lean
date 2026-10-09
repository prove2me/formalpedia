-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentCommonLiveHeight_actual_height_envelope
-- name    : OAI.SevenEighths.CenteredMomentCommonLiveHeight.actual_height_envelope
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:01.338354+00:00
-- url     : https://prove2.me/theorems/c3ce1950-fe38-4fc8-bc2d-aa9686164f04
-- title:
--   Height envelope for restricted source energies
-- statement:
--   Let $\iota$ be finite, $lo,hi:\iota\to\mathbb R$, $B\ge0$, $\delta>0$. Then there is $C_0>0$ such that for every `Input` $s$ with bounds $lo,hi$, every `Radial` datum $r$, `Supported` $C$, ideals $R$, `seed` $\mid C$, squarefree $L$, reals $E\ge0$, $Z>1$ with $N(C),N(L)\le Z^B$, $J\in\mathbb N$, a `Character` $\tau$ and $v$: if for every allocation $b$ of $C$ with nonzero frozen coefficient and every active $a$ of the common data at $L$ the `childEnergy` is at most $E(1+|v|)^{2J}$, then the `sourceRestrictedEnergy` (keep `r.keep`) over the residual pool of the coefficients $I\mapsto[C,I\text{ coprime},\ L\mid I]\,\beta(CI)$ with height coefficients `heightCoeff τ v` is at most `envelope s C L C0 Z δ E`$\cdot(1+|v|)^{2J}$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentCommonLiveHeight.actual_height_envelope` in `lean/OAI/NumberTheory/DirichletL/Moments/CommonLiveHeight.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonLiveHeight
open HeckeFamily CenteredMomentCommonRadialData
open CenteredMomentCommonRadialPointwise CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentRestrictedSource
open CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow CenteredMomentFirstSectors
open CenteredMomentCommonAllocationSum CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

open CenteredMomentCommonHeightEnvelope
open CenteredMomentSourceLiveColumn
 attribute [local instance] OAI.SevenEighths.CenteredMomentCommonLiveHeight.instDecidableEqSumFinOfNatNat_definitions
theorem actual_height_envelope (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤B) (hδ:0<δ) :
    ∃C0:ℝ,0<C0 ∧ ∀(s:Input ι),(∀i,s.lo i=lo i) → (∀i,s.hi i=hi i) →
      ∀(r:Radial) (C:Ideal O) (hC:Supported C) (R seed L:Ideal O),seed∣C → Squarefree L →
      ∀E Z:ℝ,0≤E → 1<Z → (Ideal.absNorm C:ℝ)≤Z^B → (Ideal.absNorm L:ℝ)≤Z^B →
      ∀J:ℕ,∀(τ:Character) (v:ℝ),
      (∀b:actualAllocations s.pools C,frozenCoefficient b.val C R s.ν s.W s.P≠0 → ∀a∈(commonData (withHeight s τ v) C R b).toSource.active L,
        childEnergy (commonData (withHeight s τ v) C R b) r L a≤E*(1+‖v‖)^(2*J)) →
      let Q:=finiteColumns (Fintype.piFinset s.pools)
      let β:=finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed)
      sourceRestrictedEnergy r.keep (residualPool C hC.1 Q)
        (fun I=>if IsCoprime C I ∧ L∣I then β (C*I) else 0)
        (heightCoeff τ v) r.profile r.scale≤envelope s C L C0 Z δ E*(1+‖v‖)^(2*J) := by
  sorry

end SevenEighths.CenteredMomentCommonLiveHeight

end

end OAI
end
