-- Prove2me | Theorems.Thm_OAI_SharpRamseyFive_Marking_exists_high_three_round
-- name    : OAI.SharpRamseyFive.Marking.exists_high_three_round
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T00:02:32.223593+00:00
-- url     : https://prove2.me/theorems/f0f4176c-6a7f-4114-9c92-2a191009c379
-- title:
--   OAI.SharpRamseyFive.Marking.exists_high_three_round: intermediate lemma from OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SharpRamseyFive.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170)*, OpenAI Math Release, September 24, 2026, result family 170, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SharpRamseyFive.Marking.exists_high_three_round` of [lean/OAI/Combinatorics/RamseyFive/Marking/HighChosenRound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/HighChosenRound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SharpRamseyFive.Marking`, with `open Module ProjectiveIncidence FiniteEntropy Windows CoreGeometry`, `open scoped Classical BigOperators LinearAlgebra.Projectivization`):
--
--   ```lean
--   theorem exists_high_three_round (hd : finrank K V=5)
--       (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
--       (elig : κ→Fin w×Bool→Finset (Fin n)) (rounds rem : ℕ)
--       (hrounds : 0 < rounds) (hrem : 0 < rem)
--       (hS : ∀a,0<μ a→∀b,rem+rounds≤(elig a b).card)
--       (J d ε budget s M : ℝ) (hdpos : 0<d) (hε : 0<ε)
--       (D : κ→Slots w n→Finset (FlagPair K V)) (hJ : ∀a i,Real.log (D a i).card≤J)
--       (hp : ∀a,0<μ a→InDomains (p a) (D a))
--       (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (elig a)))
--       (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (elig a)) J)≤budget)
--       (hs : 2 ≤ s) (hsmall : Real.log 32+3*s<Real.log (Nat.card K))
--       (hinc : ∀a,0<μ a→∀x,0<p a x→∀i,Incident (x i).1 (x i).2)
--       (hocc : ∀a,0<μ a→∀x,0<p a x→∀W : Submodule K (Dual K V),
--         (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
--       ∃i : Fin rounds,mean (preRoundLaw μ p elig i.val) (fun z=>
--         ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
--           preRoundBad μ p elig i.val J d ε
--             (fun a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w n) s) z j)≤
--         budget/d+(2*budget/rounds+(4*(w*(4*n):ℝ)*M)/rem)/ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.SharpRamseyFive.CoreGeometry.InRectangle`, `OAI.SharpRamseyFive.FiniteEntropy.BlockHistory`, `OAI.SharpRamseyFive.FiniteEntropy.FixedOutside`, `OAI.SharpRamseyFive.FiniteEntropy.InDomains`, `OAI.SharpRamseyFive.FiniteEntropy.Law`, `OAI.SharpRamseyFive.FiniteEntropy.activeDeficit`, `OAI.SharpRamseyFive.FiniteEntropy.blockActive`, `OAI.SharpRamseyFive.FiniteEntropy.blockHistoryFintype`, `OAI.SharpRamseyFive.FiniteEntropy.historyPosterior`, `OAI.SharpRamseyFive.FiniteEntropy.historyUnused`, `OAI.SharpRamseyFive.FiniteEntropy.mean`, `OAI.SharpRamseyFive.FiniteEntropy.preRoundBad`, `OAI.SharpRamseyFive.FiniteEntropy.preRoundLaw`, `OAI.SharpRamseyFive.Marking.FlagPair`, `OAI.SharpRamseyFive.ProjectiveIncidence.Incident` and `OAI.SharpRamseyFive.Windows.Slots` (definitions bundle `OAIQ060R000` of this split); `OAI.SharpRamseyFive.Windows.slotEquiv` (definitions bundle `OAIQ060R002` of this split); `OAI.SharpRamseyFive.Marking.hcrIDE` and `OAI.SharpRamseyFive.Marking.orderedHighCollision` (definitions bundle `OAIQ060R004` of this split).
--
--   **Used by.** The proof of `OAI.SharpRamseyFive.SelectedTuple.eventually_high_three_prepared_impossible` of this split imports it.
-- source:
--   OpenAI, Sharp logarithmic exponents for fixed off-diagonal Ramsey numbers (result family 170), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 170; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/RamseyFive/Marking/HighChosenRound.lean (declaration OAI.SharpRamseyFive.Marking.exists_high_three_round)

import Mathlib
import Definitions.Def_OAIQ060R004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpRamseyFive.Marking
open Module ProjectiveIncidence FiniteEntropy Windows CoreGeometry
open scoped Classical BigOperators LinearAlgebra.Projectivization
noncomputable section
variable {K V κ : Type} [Field K] [AddCommGroup V] [Module K V]
  [Finite K] [FiniteDimensional K V] [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
  [Fintype κ] {w n : ℕ} [Nonempty (Fin n)]

attribute [local instance] OAI.SharpRamseyFive.Marking.hcrIDE
local instance hcrBDEFix (w : ℕ) : DecidableEq (Fin w×Bool) := Classical.decEq _
local instance hcrTDEFix (w n : ℕ) : DecidableEq (Fin w×Fin (2*n)) := Classical.decEq _
theorem exists_high_three_round (hd : finrank K V=5)
    (μ : Law κ) (p : κ→Law (Slots w n→FlagPair K V))
    (elig : κ→Fin w×Bool→Finset (Fin n)) (rounds rem : ℕ)
    (hrounds : 0 < rounds) (hrem : 0 < rem)
    (hS : ∀a,0<μ a→∀b,rem+rounds≤(elig a b).card)
    (J d ε budget s M : ℝ) (hdpos : 0<d) (hε : 0<ε)
    (D : κ→Slots w n→Finset (FlagPair K V)) (hJ : ∀a i,Real.log (D a i).card≤J)
    (hp : ∀a,0<μ a→InDomains (p a) (D a))
    (hfix : ∀a,0<μ a→FixedOutside (p a) (blockActive (elig a)))
    (hbudget : mean μ (fun a=>activeDeficit (p a) (blockActive (elig a)) J)≤budget)
    (hs : 2 ≤ s) (hsmall : Real.log 32+3*s<Real.log (Nat.card K))
    (hinc : ∀a,0<μ a→∀x,0<p a x→∀i,Incident (x i).1 (x i).2)
    (hocc : ∀a,0<μ a→∀x,0<p a x→∀W : Submodule K (Dual K V),
      (∑i,if InRectangle W (x i).1.rep (x i).2.rep then (1:ℝ) else 0)≤M) :
    ∃i : Fin rounds,mean (preRoundLaw μ p elig i.val) (fun z=>
      ∑j∈blockActive (historyUnused (elig z.1.1) z.1.2),
        preRoundBad μ p elig i.val J d ε
          (fun a h=>orderedHighCollision (historyPosterior (p a) h) (slotEquiv w n) s) z j)≤
      budget/d+(2*budget/rounds+(4*(w*(4*n):ℝ)*M)/rem)/ε := by
  sorry
end
end SharpRamseyFive.Marking

end OAI
end
