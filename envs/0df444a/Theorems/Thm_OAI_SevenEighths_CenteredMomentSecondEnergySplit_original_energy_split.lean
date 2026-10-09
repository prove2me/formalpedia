-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondEnergySplit_original_energy_split
-- name    : OAI.SevenEighths.CenteredMomentSecondEnergySplit.original_energy_split
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:16.19274+00:00
-- url     : https://prove2.me/theorems/35983529-174c-4d06-990c-d642e8d03547
-- title:
--   The second retained energy splits into two parts
-- statement:
--   For a `Character` $\eta$, a ray character $\chi$, $Q$, $m$, $t$, $S$, $\beta$ with support of norm $\le H$, a Schwartz $W$ and reals $K>0$, $T_{\mathrm{sec}},Z,\xi$: `secondRetainedEnergy η t S β W K Tsec Z ξ` $=$ `partEnergy true … H` $+$ `partEnergy false … H`.
--
--   Lean: `OAI.SevenEighths.CenteredMomentSecondEnergySplit.original_energy_split` in `lean/OAI/NumberTheory/DirichletL/Moments/SecondEnergySplit.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondEnergySplit
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondLiveBlock CenteredMomentSecondBlockAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit
open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization
open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource
open CenteredMomentFirstSectors CenteredMomentSourceRow CenteredMomentRestrictedEnergy
open CenteredMomentChildRows RayFourExpansion
local notation "O"=>HeckeFamily.O

theorem original_energy_split (η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)
    (S:Finset (Ideal O))(β:Ideal O→ℂ)(W:𝓢(ℝ,ℂ))(K Tsec Z ξ H:ℝ)(hK:0<K)
    (hH:∀I∈S,β I≠0→(I.absNorm:ℝ)≤H):
    secondRetainedEnergy η t S β W K Tsec Z ξ=
      partEnergy true η χ Q m t S β W K Tsec Z ξ H+
      partEnergy false η χ Q m t S β W K Tsec Z ξ H:= by
  sorry

end SevenEighths.CenteredMomentSecondEnergySplit

end

end OAI
end
