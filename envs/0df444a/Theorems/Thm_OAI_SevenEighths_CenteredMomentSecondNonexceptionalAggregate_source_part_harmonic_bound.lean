-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSecondNonexceptionalAggregate_source_part_harmonic_bound
-- name    : OAI.SevenEighths.CenteredMomentSecondNonexceptionalAggregate.source_part_harmonic_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:21:41.610242+00:00
-- url     : https://prove2.me/theorems/2f919198-67d5-4e15-af7c-a17c5b2d279d
-- title:
--   Part energies bounded through block bounds and harmonic sums
-- statement:
--   For $B,L\ge0$, $C_r,\varepsilon>0$ there is $C>0$ such that eventually in $Z$: for every squarefree nonzero `seed`, finite $S$ and $\beta$ whose nonzero values sit on multiples of `seed` of norm $\le Z^B$, every Boolean `exceptional`, `Character` $\eta$, ray character $\chi$, $Q$, $m$, $t$, Schwartz $W$, reals $K>0$, $T_{\mathrm{sec}},\xi$ with `frequencyRadius Tsec Z ξ` $\le C_rZ^L$, $H\le Z^B$, $V>0$, $E\ge0$: if every `physicalBlock` over the part rows (for live labels $p$, subsets $U$, source blocks $n$) has norm $\le E\cdot V\cdot$`pairWeight p₁ p₂`, then $\|\texttt{partEnergy}\ \mathrm{exceptional}\ \eta\,\chi\,Q\,m\,t\,S\,\beta\,W\,K\,T_{\mathrm{sec}}\,Z\,\xi\,H\|/V\le E\,C\,Z^{\varepsilon}/N(\mathrm{seed})$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentSecondNonexceptionalAggregate.source_part_harmonic_bound` in `lean/OAI/NumberTheory/DirichletL/Moments/SecondNonexceptionalAggregate.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

namespace SevenEighths.CenteredMomentSecondNonexceptionalAggregate
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentSecondEnergySplit CenteredMomentSecondLiveBlock
open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate
open CenteredMomentSecondPhysicalBlock CenteredMomentSecondCanonical
open CenteredMomentCanonicalFirst CenteredMomentSecondCanonicalNonunit
open CenteredMomentSectorLocalization CenteredMomentActiveSource
open CenteredMomentSecondBlockHarmonicMass
open CenteredMomentFirstSectors CenteredMomentSourceRow RayFourExpansion
local notation "O"=>HeckeFamily.O

local instance instDecidableEqSumFinOfNatNat_solutions_r2f076f_1 {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _
theorem source_part_harmonic_bound (B L Cr ε:ℝ)(hB:0≤B)(hL:0≤L)
    (hCr:0<Cr)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in Filter.atTop,
    ∀(seed:Ideal O),Squarefree seed → seed≠0 →
    ∀(S:Finset (Ideal O))(β:Ideal O→ℂ),
    (∀I∈S,β I≠0→seed∣I) → (∀I∈S,β I≠0→(I.absNorm:ℝ)≤Z^B) →
    ∀(exceptional:Bool)(η:Character)(χ:RayCharacter)(Q:Ideal O)(m:O)(t:ℝ)(W:𝓢(ℝ,ℂ))
      (K Tsec ξ H V E:ℝ),0<K → frequencyRadius Tsec Z ξ≤Cr*Z^L → H≤Z^B → 0<V → 0≤E →
    (∀p∈liveLabels η S β,∀U:Finset (CommonIndex p.val.1 p.val.2),
      ∀n:SourceBlocks p.val.1 p.val.2 U K (frequencyRadius Tsec Z ξ) H,
      ‖physicalBlock η t (activeSource S β) β p.val.1 p.val.2
        (commonLabels_supported (activeSource S β) _ _ p.property).1
        (commonLabels_supported (activeSource S β) _ _ p.property).2 U
        (frequencyRadius Tsec Z ξ)
        (partRows exceptional η χ Q m p.val.1 p.val.2 U (frequencyRadius Tsec Z ξ))
        W K (fun i=>(n i:ℤ))‖/V≤E*pairWeight p.val.1 p.val.2) →
    ‖partEnergy exceptional η χ Q m t S β W K Tsec Z ξ H‖/V≤E*(C*Z^ε/(seed.absNorm:ℝ)):= by
  sorry

end SevenEighths.CenteredMomentSecondNonexceptionalAggregate

end

end OAI
end
