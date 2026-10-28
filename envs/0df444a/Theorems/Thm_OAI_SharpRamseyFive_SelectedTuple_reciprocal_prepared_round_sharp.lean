-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_SelectedTuple_reciprocal_prepared_round_sharp
-- name    : OAI.SharpRamseyFive.SelectedTuple.reciprocal_prepared_round_sharp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:09:31.257895+00:00
-- url     : https://prove2.me/theorems/44d7400d-5d2f-4b9b-826a-e8388007327d
-- title:
--   OAI.SharpRamseyFive.SelectedTuple.reciprocal_prepared_round_sharp: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.SelectedTuple.reciprocal_prepared_round_sharp` of [lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalSharpRound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalSharpRound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.SelectedTuple`, with `open Module ProjectiveIncidence FiniteEntropy Windows Marking`, `open scoped Classical BigOperators LinearAlgebra.Projectivization`):
--
--   ```lean
--   theorem reciprocal_prepared_round_sharp (hd : finrank K V=5)
--       (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
--       (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
--       (rounds rem : ℕ) (hrounds : 0 < rounds) (hrem : 0 < rem) (hroom : rem+rounds≤n)
--       (d s ε width : ℝ) (hdp : 0<d) (hs : 2 ≤ s) (he : 0<ε) (_hM : 0≤M)
--       (u : κ→Slots w n→ℝ) (b : Fin 7)
--       (hband : ∀c,0 < map S.law ctx c→∀i,BandCondition (Real.log (Nat.card K)) width (u c i) b)
--       (hsmall : Real.log 32+width+3*s<Real.log (Nat.card K))
--       (hwide : Real.log 32+3*s<width) :
--       ∃i : Fin rounds,mean (preRoundLaw (first (pair S.law ctx (windowTuple S)))
--         (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val) (fun z=>
--         ∑j∈blockActive (historyUnused (fun _=>Finset.univ) z.1.2),
--           preRoundBad (first (pair S.law ctx (windowTuple S)))
--             (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val J d ε
--             (historyCollision (fiber (pair S.law ctx (windowTuple S))) u s) z j)≤
--         B/d+(2*B/rounds+(if b.val%2=0 then (4*(w*(4*n):ℝ)*M)/rem else 0))/ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.FiniteEntropy.BlockHistory`, `OAI.SharpRamseyFive.FiniteEntropy.blockActive`, `OAI.SharpRamseyFive.FiniteEntropy.blockHistoryFintype`, `OAI.SharpRamseyFive.FiniteEntropy.fiber`, `OAI.SharpRamseyFive.FiniteEntropy.first`, `OAI.SharpRamseyFive.FiniteEntropy.historyUnused`, `OAI.SharpRamseyFive.FiniteEntropy.map`, `OAI.SharpRamseyFive.FiniteEntropy.mean`, `OAI.SharpRamseyFive.FiniteEntropy.pair`, `OAI.SharpRamseyFive.FiniteEntropy.preRoundBad`, `OAI.SharpRamseyFive.FiniteEntropy.preRoundDeletionIndexDecEq`, `OAI.SharpRamseyFive.FiniteEntropy.preRoundLaw`, `OAI.SharpRamseyFive.FiniteEntropy.uniformHistoryIndexDecEq`, `OAI.SharpRamseyFive.Marking.FlagPair`, `OAI.SharpRamseyFive.SelectedTuple.SelectedStream`, `OAI.SharpRamseyFive.Windows.Slots` and `OAI.SharpRamseyFive.FiniteEntropy.Law` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.Marking.BandCondition` (definitions bundle `OAIQ060R001` of this split); `OAI.SharpRamseyFive.Marking.histWinIDE`, `OAI.SharpRamseyFive.Marking.historyCollision` and `OAI.SharpRamseyFive.SelectedTuple.Prepared` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.SelectedTuple.rprIDE` and `OAI.SharpRamseyFive.SelectedTuple.windowTuple` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_reciprocal_coded_stage` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/ReciprocalSharpRound.lean (declaration OAI.SharpRamseyFive.SelectedTuple.reciprocal_prepared_round_sharp)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.SelectedTuple

section
open Module ProjectiveIncidence FiniteEntropy Windows Marking
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V Ω κ α : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype Ω] [Fintype κ] [Fintype α]
  {N w n : ℕ} [Nonempty (Fin n)] {admissible : (Fin N→α)→Prop}

attribute [local instance] OAI.SharpRamseyFive.SelectedTuple.rprIDE
local instance rprBDEFix (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance rprTDEFix (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
theorem reciprocal_prepared_round_sharp (hd : finrank K V=5)
    (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N (w*(4*n)) admissible)
    (ctx : Ω→κ) (J B M : ℝ) (P : Prepared S ctx J B M)
    (rounds rem : ℕ) (hrounds : 0 < rounds) (hrem : 0 < rem) (hroom : rem+rounds≤n)
    (d s ε width : ℝ) (hdp : 0<d) (hs : 2 ≤ s) (he : 0<ε) (_hM : 0≤M)
    (u : κ→Slots w n→ℝ) (b : Fin 7)
    (hband : ∀c,0 < map S.law ctx c→∀i,BandCondition (Real.log (Nat.card K)) width (u c i) b)
    (hsmall : Real.log 32+width+3*s<Real.log (Nat.card K))
    (hwide : Real.log 32+3*s<width) :
    ∃i : Fin rounds,mean (preRoundLaw (first (pair S.law ctx (windowTuple S)))
      (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val) (fun z=>
      ∑j∈blockActive (historyUnused (fun _=>Finset.univ) z.1.2),
        preRoundBad (first (pair S.law ctx (windowTuple S)))
          (fiber (pair S.law ctx (windowTuple S))) (fun _ _=>Finset.univ) i.val J d ε
          (historyCollision (fiber (pair S.law ctx (windowTuple S))) u s) z j)≤
      B/d+(2*B/rounds+(if b.val%2=0 then (4*(w*(4*n):ℝ)*M)/rem else 0))/ε := by
  sorry
end
end

open Module ProjectiveIncidence FiniteEntropy Windows Marking PivotTree ReverseCap ScoreGeometry
open ParameterHierarchy Filter
open scoped Classical BigOperators LinearAlgebra.Projectivization Topology NNReal

end SharpRamseyFive.SelectedTuple

end OAI
end
