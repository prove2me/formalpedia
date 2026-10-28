-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_high_prepared_round
-- name    : OAI.SharpRamseyFive.SelectedTuple.high_prepared_round
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:09:27.991338+00:00
-- url     : https://prove2.me/theorems/a7238134-95d1-42c7-bd69-e35607c1c728
-- title:
--   OAI.SharpRamseyFive.SelectedTuple.high_prepared_round: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.SelectedTuple.high_prepared_round` of [lean/OAI/Combinatorics/RamseyFive/Streams/HighSampleContradiction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Streams/HighSampleContradiction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.SelectedTuple`, with `open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples`, `open scoped Classical BigOperators LinearAlgebra.Projectivization`):
--
--   ```lean
--   theorem high_prepared_round (hd : finrank K V=5)
--       (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
--       (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
--       (r' : ℕ) (hr' : r'≤4)
--       (hcap : ∀c,0 < map S.law ctx c→∀i,HighCaps (P.domain c i) 4 r')
--       (rounds rem : ℕ) (hrounds : 0 < rounds) (hrem : 0 < rem)
--       (hn : n≤2*rem) (hroom : rem+rounds≤n)
--       (d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hdp : 0<d) (hs : 0 < s) (he : 0<ε)
--       (hbad : highBadMass s d 153≤(1:ℝ)/4)
--       (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
--       (h : ℕ) :
--       ∃i : Fin rounds,
--         mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
--           (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val)
--           (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
--           (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
--             5*(B/d+(2*B/rounds)/(ε))+(2*n:ℝ)*highFourLoss (Nat.card K) r' h s d ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.BlockHistory`, `OAI.SharpRamseyFive.FiniteEntropy.adaptiveLaw`, `OAI.SharpRamseyFive.FiniteEntropy.blockHistoryFintype`, `OAI.SharpRamseyFive.FiniteEntropy.coveredPositions`, `OAI.SharpRamseyFive.FiniteEntropy.fiber`, `OAI.SharpRamseyFive.FiniteEntropy.first`, `OAI.SharpRamseyFive.FiniteEntropy.highBadMass`, `OAI.SharpRamseyFive.FiniteEntropy.historyProducerIndexDecEq`, `OAI.SharpRamseyFive.FiniteEntropy.map`, `OAI.SharpRamseyFive.FiniteEntropy.mean`, `OAI.SharpRamseyFive.FiniteEntropy.pair`, `OAI.SharpRamseyFive.FiniteEntropy.preRoundTupleLaw`, `OAI.SharpRamseyFive.Marking.FlagPair`, `OAI.SharpRamseyFive.SelectedTuple.SelectedStream`, `OAI.SharpRamseyFive.Windows.Slots` and `OAI.SharpRamseyFive.FiniteEntropy.Law` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.HighSamples.highDomain`, `OAI.SharpRamseyFive.Marking.HighCaps` and `OAI.SharpRamseyFive.SelectedTuple.Prepared` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.Marking.highFourLoss`, `OAI.SharpRamseyFive.Marking.highFourPreIndexDE` and `OAI.SharpRamseyFive.Marking.highFourSampler` (definitions bundle `OAIQ060R003` of this split); `OAI.SharpRamseyFive.SelectedTuple.hprIDE` and `OAI.SharpRamseyFive.SelectedTuple.windowTuple` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_high_prepared_impossible` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Streams/HighSampleContradiction.lean (declaration OAI.SharpRamseyFive.SelectedTuple.high_prepared_round)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

open Module ProjectiveIncidence FiniteEntropy Windows Marking HighSamples
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype (ℙ K (Dual K (Dual K V)))]
  [Nonempty (ℙ K V)] [Nonempty (ℙ K (Dual K V))]
  [Nonempty (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α]
  {N n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.hprIDE
local instance hprBDEFix (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance hprTDEFix (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
omit [Fintype (ℙ K (Dual K (Dual K V)))] [Nonempty (ℙ K V)]
  [Nonempty (ℙ K (Dual K V))] [Nonempty (ℙ K (Dual K (Dual K V)))] in
theorem high_prepared_round (hd : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (1*(4*n)) admissible)
    (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
    (r' : ℕ) (hr' : r'≤4)
    (hcap : ∀c,0 < map S.law ctx c→∀i,HighCaps (P.domain c i) 4 r')
    (rounds rem : ℕ) (hrounds : 0 < rounds) (hrem : 0 < rem)
    (hn : n≤2*rem) (hroom : rem+rounds≤n)
    (d s ε : ℝ) (hJ : 4*Real.log (Nat.card K)≤J) (hdp : 0<d) (hs : 0 < s) (he : 0<ε)
    (hbad : highBadMass s d 153≤(1:ℝ)/4)
    (hsmall : 2*(Nat.card K:ℝ)^2*(2*Real.exp s/(Nat.card K:ℝ)^4)≤1/(20*(Nat.card K:ℝ)))
    (h : ℕ) :
    ∃i : Fin rounds,
      mean (adaptiveLaw (preRoundTupleLaw (first (pair S.law ctx (windowTuple S)))
        (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val)
        (fun z=>highFourSampler (fiber (pair S.law ctx (windowTuple S))) r' s h z.1))
        (fun z=>((coveredPositions (fun t=>z.1.2 (Sum.inr (0,t))) (highDomain z.2))ᶜ.card:ℝ))≤
          5*(B/d+(2*B/rounds)/(ε))+(2*n:ℝ)*highFourLoss (Nat.card K) r' h s d ε := by
  sorry
end

end SharpRamseyFive.SelectedTuple

end OAI
end
