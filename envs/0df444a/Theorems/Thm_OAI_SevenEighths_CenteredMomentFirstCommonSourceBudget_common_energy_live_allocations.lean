-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstCommonSourceBudget_common_energy_live_allocations
-- name    : OAI.SevenEighths.CenteredMomentFirstCommonSourceBudget.common_energy_live_allocations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:48.778287+00:00
-- url     : https://prove2.me/theorems/10d3bfb9-11c0-48f7-83a1-4b815b2898e7
-- title:
--   Common energy split over live allocations
-- statement:
--   For $N$, $a>0$, $b$, an `Input` $s$ with at most $N$ slots, $a\le s.\mathrm{lower}$, $s.\mathrm{upper}\le b$, `Supported` $C$, $R$, `seed` $\mid C$, a `Character` $\tau$, $t$, $L$, a Schwartz $W$ and $K>0$ with $\operatorname{Re}W(\|\texttt{eisEmbedding}\,z\|^2/K)\ge0$:
--   $$\frac{\operatorname{Re}\texttt{commonEnergy}(\texttt{original}\,s\,R\,\mathrm{seed})\,C\,\tau\,t\,L\,W\,K}{\texttt{volume}\,s}\le\frac{\max(1,b)^N|\texttt{actualAllocations}|}{N(C)}\sum_{B:\ \text{frozen coefficient}\ne0}(\texttt{frozenControl}\,B\,s.M)^2\,\texttt{childNormalizedGaussSource}\,s\,C\,R\,L\,B\,\tau\,t\,W\,K.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentFirstCommonSourceBudget.common_energy_live_allocations` in `lean/OAI/NumberTheory/DirichletL/Moments/FirstCommonSourceBudget.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

namespace SevenEighths.CenteredMomentFirstCommonSourceBudget
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput CenteredMomentFirstPhysicalSource
open CenteredMomentFirstAmplificationChoice CenteredMomentCommonAllocationSum
open CenteredMomentCommonRawScale CenteredMomentSourceLiveColumn CenteredMomentFirstAllocationGaussEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]

local instance instDecidableEq_solutions_rcbe672_1 {κ:Type*}:DecidableEq κ:=Classical.decEq _
theorem common_energy_live_allocations (N:ℕ)(a b:ℝ)(ha:0<a)
    (s:Input ι)(hcard:Fintype.card ι≤N)(haS:a≤ s.lower)(hbS:s.upper≤b)
    (C R seed:Ideal O)(hC:Supported C)(hseed:seed∣C)
    (τ:Character)(t:ℝ)(L:Ideal O)(W:𝓢(ℝ,ℂ))(K:ℝ)(hK:0<K)
    (hW:∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re):
    (CenteredMomentFirstPhysicalSource.commonEnergy (original s R seed) C hC τ t L W K).re/
      CenteredMomentAmplificationChildInput.volume s≤
    (max 1 b)^N*((actualAllocations s.pools C).card:ℝ)/(C.absNorm:ℝ)*
      ∑B:actualAllocations s.pools C,
        if frozenCoefficient B.val C R s.ν s.W s.P≠0 then
          (frozenControl B.val s.M)^2*childNormalizedGaussSource s C R L B τ t W K
        else 0:= by
  sorry

end SevenEighths.CenteredMomentFirstCommonSourceBudget

end

end OAI
end
