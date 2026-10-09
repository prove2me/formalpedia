-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyAllocatedChildren_actual_common_from_energy
-- name    : OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren.actual_common_from_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:24:06.516979+00:00
-- url     : https://prove2.me/theorems/ed040319-fa5f-485a-807b-a92c380211de
-- title:
--   Child energies of common data from allocated energies
-- statement:
--   Let $\alpha$ be finite, $b,M\ge0$ on $\alpha$, $\varepsilon>0$. Then there is $C_0>0$ such that for every `Input` $s$ with $s.hi\le b$, $s.M\le M$, `Character` $\tau$, $v$, ideals $C$, $R\ne0$, allocation $B$ of $C$, ideal $L$ and allocation $a$ of $L$, `Plain` data $V_1,V_2$ with tests $s.W_1,s.W_2$, a `Radial` $r$ keeping only nonzero elements, and $E_1,E_2\ge0$ bounding every `commonAllocatedEnergy … left D₁ D₂ J` (by $E_1$ for left, $E_2$ for right, $D_1,D_2$ over subsets of the prime support of $RC$, $J$ over live indices): `childEnergy (commonData (withHeight s τ v) C R B) r L a` $\le C_0N(\operatorname{rad}(RC))^{\varepsilon}(E_1+E_2)$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyAllocatedChildren.actual_common_from_energy` in `lean/OAI/NumberTheory/DirichletL/Energy/AllocatedBound.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentNaturalRowSource CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem actual_common_from_energy (b M:α→ℝ)(hM:∀i,0≤M i)(ε:ℝ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀s:Input α,(∀i,s.hi i≤b i)→(∀i,s.M i≤M i)→
    ∀(τ:Character)(v:ℝ)(C R:Ideal O),R≠0→∀B:actualAllocations s.pools C,
    ∀(L:Ideal O)(a:Allocation L (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂:Plain,V₁.W=s.W₁→V₂.W=s.W₂→∀r:Radial,(∀z,r.keep z→z≠0)→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀left:Bool,∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
      ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      commonAllocatedEnergy s τ v C R B L a V₁ V₂ r left D₁ D₂ J≤(if left then E₁ else E₂))→
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂):= by
  sorry

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI
end
