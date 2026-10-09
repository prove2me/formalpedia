-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSourceInputFirstSectorTail_local_input_tail
-- name    : OAI.SevenEighths.CenteredMomentSourceInputFirstSectorTail.local_input_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:22:37.50944+00:00
-- url     : https://prove2.me/theorems/845fcb8e-0182-4710-8e2b-6483f16b3bc9
-- title:
--   The discarded first-sector energy is negligible
-- statement:
--   With $\iota$, $hi$, $w_{lo},w_{hi},B$, $\xi>0$, `saving` as above, there are a finite $S_\Phi$ and $C>0$ such that for all sufficiently large $Z$, every `Input` $s$ with tests supported in $[w_{lo},w_{hi}]$ and $s.hi\le hi$, all $m,A,R,\mathrm{seed}$, Schwartz $\Phi$ and $K>0$ with `volume s.toData` $\le Z^B$, $K^{-1}\le Z^B$: $\|\texttt{discardedEnergy}(\dots,\texttt{volume}\,s,Z,\xi)\|/\texttt{volume}\,s\le C\,\texttt{plainControl}^2\|\Phi\|_{S_\Phi}K\,Z^{-\mathrm{saving}}$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentSourceInputFirstSectorTail.local_input_tail` in `lean/OAI/NumberTheory/DirichletL/Moments/SourceInputFirstSectorTailNatural.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy
open CenteredMomentSourceProfileMass
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization
open CenteredMomentExceptionalAmplitudePair
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputFirstSectorTail.instDecidableEqSumFinOfNatNat_definitions_1
omit [DecidableEq ι] in
theorem local_input_tail (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  sorry

end SevenEighths.CenteredMomentSourceInputFirstSectorTail

end

end OAI
end
