-- Prove2me | Theorems.Thm_OAI_SevenEighths_CenteredMomentFirstPhysicalDyadicCount_original_input_local_blocks_subpower
-- name    : OAI.SevenEighths.CenteredMomentFirstPhysicalDyadicCount.original_input_local_blocks_subpower
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T02:21:53.43102+00:00
-- url     : https://prove2.me/theorems/8f4c1bbe-a3dc-4b23-a04d-fb9acf1523da
-- title:
--   The number of local blocks is a subpower
-- statement:
--   Let $\iota$ be finite, $hi:\iota\to\mathbb R$, reals $b_1,b_2$, $B\ge0$, $\xi\ge0$, $\varepsilon>0$. Then there is $C_0>0$ such that for all sufficiently large $Z$: for every `Input` $s$ with $|s.hi_i|\le hi_i$, $|s.b_1|\le b_1$, $|s.b_2|\le b_2$ and positive `sourceRadius s`, all nonzero ideals $C,D$, every $E\subseteq$`CommonIndex C D` and $K>0$ with `volume s.toData` $\le Z^B$ and $K^{-1}\le Z^B$, the number of `Blocks` (at `effectiveScale C D E K`, `frequencyRadius (firstNominalScale …) Z ξ`, `sourceRadius s / N(C)`, `sourceRadius s / N(D)`) is at most $C_0Z^\varepsilon$.
--
--   Lean: `OAI.SevenEighths.CenteredMomentFirstPhysicalDyadicCount.original_input_local_blocks_subpower` in `lean/OAI/NumberTheory/DirichletL/Moments/FirstPhysicalDyadicCountSource.lean` (OpenAI); the definitions it uses are in the definitions bundles of this split (OpenAI's, carved) and in wurtle's bundle `HeckeSevenEighths`.
-- source:
--   OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8, OpenAI Math Release, September 30, 2026, family 003 of https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory/DirichletL

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B025

section

namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicCount
open CenteredMomentFirstPhysicalDyadicAssembly CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentSectorLocalization
local notation "O"=>ActualEisensteinCubic.O

open CenteredMomentCommonRadialData CenteredMomentOriginalCommonHarmonic
open CenteredMomentExceptionalAmplitudePair

theorem original_input_local_blocks_subpower {ι:Type*}[Fintype ι][DecidableEq ι]
    (hi:ι→ℝ)(b₁ b₂ B ξ ε:ℝ)(hB:0≤B)(hξ:0≤ξ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀s:Input ι,(∀i,|s.hi i|≤hi i)→|s.b₁|≤b₁→|s.b₂|≤b₂→0<sourceRadius s→
      ∀(C D:Ideal O),C≠0→D≠0→∀(E:Finset (CommonIndex C D))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      (Fintype.card (Blocks (effectiveScale C D E K)
        (frequencyRadius (firstNominalScale C D (∏P∈E,P.val) K (volume s.toData)) Z ξ)
        (sourceRadius s/Ideal.absNorm C) (sourceRadius s/Ideal.absNorm D)):ℝ)≤C₀*Z^ε := by
  sorry

end SevenEighths.CenteredMomentFirstPhysicalDyadicCount

end

end OAI
end
