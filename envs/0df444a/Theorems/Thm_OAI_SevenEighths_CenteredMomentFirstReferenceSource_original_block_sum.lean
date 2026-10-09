-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstReferenceSource_original_block_sum
-- name    : OAI.SevenEighths.CenteredMomentFirstReferenceSource.original_block_sum
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:25:56.227766+00:00
-- url     : https://prove2.me/theorems/4924e09d-7169-4c77-ab61-8e8acd951f1b
-- title:
--   Physical mass from bounds on the original blocks
-- statement:
--   For $\iota$ finite, $hi$, $b_1,b_2$, $B,\xi\ge0$, $\varepsilon>0$ there is $C_0>0$ such that eventually in $Z$: for every `Input` $s$ with tests vanishing at $0$, $|s.hi|\le hi$, $|s.b_k|\le b_k$, positive `sourceRadius`, squarefree nonzero `seed`, $R$, Schwartz $W$, $K>0$, $A\ge0$ with `volume` $\le Z^B$, $K^{-1}\le Z^B$: if every `originalBlock` (label $p$, inactive subset $E$, source block $n$) has $\|\cdot\|/\texttt{volume}\,s\le A\cdot$`radicalWeight s R seed p E`, then the `physicalMass` (with mask `fixedBadMask·idealGenerator R`) divided by `volume s` is at most $A\,C_0Z^{\varepsilon}/N(\mathrm{seed})$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentFirstReferenceSource.original_block_sum` in `lean/OAI/NumberTheory/DirichletL/Moments/FirstReferenceSource.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

namespace SevenEighths.CenteredMomentFirstReferenceSource
open ActualEisensteinCubic HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentFirstPhysicalSource CenteredMomentFirstPhysicalDyadicAssembly
open CenteredMomentFirstRetainedNorm
open CenteredMomentFirstNonexceptionalWeightSum CenteredMomentFirstNonexceptionalLocalWeightSum
open CenteredMomentFirstSourceReduction
open CenteredMomentFirstInactiveRadicalMass CenteredMomentFirstDiscardedEnergy
open CenteredMomentSecondRetainedAggregate CenteredMomentActiveSource CenteredMomentSourceRow
open CenteredMomentSourceMass CenteredMomentCanonicalFirst CenteredMomentFirstSectors
open CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization CenteredMomentLogDyadic
open CenteredMomentExceptionalAmplitudePair CenteredMomentRankinRadical
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentFirstReferenceSource.instDecidableEqSumFinOfNatNat_solutions
theorem original_block_sum (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)
    (hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in atTop,∀s:Input ι,∀R seed:Ideal O,
      Squarefree seed→seed≠0→s.W₁ 0=0→s.W₂ 0=0→
      (∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
    ∀W:𝓢(ℝ,ℂ),∀K A:ℝ,0<K→0≤A→volume s.toData≤Z^B→K⁻¹≤Z^B→
    (∀p:Labels s R seed,∀E∈inactiveSubsets p.val.1 p.val.2,
      ∀n:SourceBlocks s R seed K Z ξ p E,
      ‖originalBlock s R seed W K Z ξ p E n‖/volume s.toData≤A*radicalWeight s R seed p E)→
    physicalMass s R seed (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 W K Z ξ/
      volume s.toData≤A*(C₀*Z^ε/(seed.absNorm:ℝ)) := by
  sorry

end SevenEighths.CenteredMomentFirstReferenceSource

end

end OAI
end
