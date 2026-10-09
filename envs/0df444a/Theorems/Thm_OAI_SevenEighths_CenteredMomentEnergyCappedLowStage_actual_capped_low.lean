-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentEnergyCappedLowStage_actual_capped_low
-- name    : OAI.SevenEighths.CenteredMomentEnergyCappedLowStage.actual_capped_low
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:25:07.372255+00:00
-- url     : https://prove2.me/theorems/d0c0471a-8033-45c5-a142-4743884d6a20
-- title:
--   The capped low stage holds at every band
-- statement:
--   For a smooth slot weight $W$ on $[a_{\mathrm{slot}},b_{\mathrm{slot}}]$ ($a_{\mathrm{slot}}>0$, $b_{\mathrm{slot}}\ge0$), reals $a>0$, $b\ge0$, `radial` $\ge2$, $B_{\mathrm{mask}},M_{\mathrm{cap}}\ge0$, $L$, $lo,hi$, $\kappa\ge3/4$, $\varepsilon>0$ and $\beta\ge51/100$ (with the remaining hypotheses of the Lean), there are constants such that for every band index $k$ both `PositiveLowAt` and `ZeroLowAt` hold at the next band: at `lowerAt a b Mcap ε (k+1)`, `requestLength Mcap Bmask (lengthAt … (k+1))`, mesh `fineMesh`, `bandWidth … (k+1)` and `physicalLoss … k`.
--
--   Lean: `OAI.SevenEighths.CenteredMomentEnergyCappedLowStage.actual_capped_low` in `lean/OAI/NumberTheory/DirichletL/Energy/CappedLowStage.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B026

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentEnergyCappedLowStage
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthInduction
open CenteredMomentEnergyWidthSchedule CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyStageReserveSchedule CenteredMomentEnergyStageMargins
open CenteredMomentEnergyBandMonotonicity CenteredMomentEnergyReferenceLowBands
open CenteredMomentEnergyCappedRequests
open CenteredMomentNaturalFixedRaySource
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

local instance instFiniteQuotientOIdeal_solutions_r3ed3f9_1 : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
theorem actual_capped_low
    (W:ℝ→ℂ)(aslot bslot a b radial Bmask L lo hi Mcap κ ε:ℝ)
    (hW:ContDiff ℝ ∞ W)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hbslot:0≤bslot)
    (ha:0<a)(hb:0≤b)(hrad:2≤ radial)(hmask:0≤Bmask)(hMcap:0≤Mcap)
    (hκ:(3/4:ℝ)≤κ)(hε:0<ε)(hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)
    (hκbeta:2*HeckeZeroSupremum.beta-1≤κ)(k:ℕ)(hk:k<count Mcap ε)
    (hold:CenteredMomentEnergyCappedWidthInduction.CertifiedBand (α:=α) M H hH
      W bslot a b radial Bmask L lo hi Mcap κ ε k):
    ∃U:Finset (ℕ×ℕ),∃J:ℕ,∀η₀:Character,∀Q:Ideal O,Q≤M→
      internalQ Q η₀≠0→internalQ Q η₀≠⊤→internalQ Q η₀≤Ideal.span {(72:O)}→
      ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
        PositiveLowAt (α:=α) M H hH W bslot (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (fineMesh Mcap Bmask L κ ε) lo hi
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) κ Z η₀ Q J U C ∧
        ZeroLowAt (internalQ Q η₀) (lowerAt a b Mcap ε (k+1)) b radial Bmask
          (requestLength Mcap Bmask (lengthAt Mcap Bmask L ε (k+1)))
          (bandWidth Mcap (finalSourceCap Mcap Bmask L ε) ε (k+1))
          (physicalLoss Mcap (finalSourceCap Mcap Bmask L ε) ε k) Z J U C := by
  sorry

end SevenEighths.CenteredMomentEnergyCappedLowStage

end

end OAI
end
