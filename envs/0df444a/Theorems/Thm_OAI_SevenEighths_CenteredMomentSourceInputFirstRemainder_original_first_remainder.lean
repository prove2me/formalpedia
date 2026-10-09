-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentSourceInputFirstRemainder_original_first_remainder
-- name    : OAI.SevenEighths.CenteredMomentSourceInputFirstRemainder.original_first_remainder
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:23:51.441163+00:00
-- url     : https://prove2.me/theorems/771402a2-cca3-447e-a6c8-b907ac5a68d4
-- title:
--   The finite Hecke energy minus its retained part is small
-- statement:
--   Let $\iota$ be finite, $hi\ge0$ on $\iota$, $w_{lo}>0$, $w_{hi},B\ge0$, $\varepsilon,\xi>0$, `saving`. Then there are finite $S_{\mathrm{diag}},S_{\mathrm{tail}}$ and $C_{\mathrm{diag}},C_{\mathrm{tail}}>0$ such that for all sufficiently large $Z$: for every `Input` $s$ with Schwartz tests $W_1,W_2$ supported in $[w_{lo},w_{hi}]$ and $s.hi\le hi$, all $m,A$ with `goodLambda`$\mid m$, $2\mid m$, ideals $R$, `seed`, Schwartz $\Phi$ and $K>0$ with `volume s.toData` $\le Z^B$, $K^{-1}\le Z^B$:
--   $$\frac{\|\texttt{finiteHeckeEnergy}(\dots)-\texttt{retainedEnergy}(\dots,\texttt{volume}\,s,Z,\xi)\|}{\texttt{volume}\,s}\le C_{\mathrm{diag}}\,\texttt{plainControl}^2\,\|\Phi\|_{S_{\mathrm{diag}}}K\,Z^\varepsilon+C_{\mathrm{tail}}\,\texttt{plainControl}^2\,\|\Phi\|_{S_{\mathrm{tail}}}K\,Z^{-\mathrm{saving}}.$$
--
--   Lean: `OAI.SevenEighths.CenteredMomentSourceInputFirstRemainder.original_first_remainder` in `lean/OAI/NumberTheory/DirichletL/Moments/SourceInputFirstRemainder.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
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

namespace SevenEighths.CenteredMomentSourceInputFirstRemainder
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow
open CenteredMomentExceptionalAmplitudePair CenteredMomentSourceInputTailUniform
open CenteredMomentSourceInputZeroUniform CenteredMomentSourceInputFirstSectorTail
open EisensteinSchwartzPoisson
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

attribute [local instance] OAI.SevenEighths.CenteredMomentSourceInputFirstRemainder.instDecidableEqSumFinOfNatNat_definitions
omit [DecidableEq ι] in
theorem original_first_remainder (hi:ι→ℝ)(wlo whi B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,0<Cdiag ∧ 0<Ctail ∧
      ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),
      s.W₁=W₁→s.W₂=W₂→Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→(∀i,s.hi i≤hi i)→
      ∀(m A:O),ConcretePrimeRowBridge.goodLambda∣m→(2:O)∣m→
      ∀(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖finiteHeckeEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
          (coefficient s R seed) Φ K-
        CenteredMomentFirstSectorLocalization.retainedEnergy s.η m A s.t
          (finiteColumns (Fintype.piFinset s.pools)) (coefficient s R seed) Φ K
          (volume s.toData) Z ξ‖/volume s.toData≤
      Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^ε+
      Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving):= by
  sorry

end SevenEighths.CenteredMomentSourceInputFirstRemainder

end

end OAI
end
