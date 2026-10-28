-- Prove2me | Theorems.Thm_OAI_PlanarUnitDistances_IncidenceEstimates_upper
-- name    : OAI.PlanarUnitDistances.IncidenceEstimates.upper
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T02:57:23.396207+00:00
-- url     : https://prove2.me/theorems/44c7d008-0fab-4a1e-9a04-18b6f34588bf
-- title:
--   OAI.PlanarUnitDistances.IncidenceEstimates.upper: intermediate lemma from OpenAI, A power saving for planar unit distances
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarUnitDistances.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A power saving for planar unit distances*, OpenAI Math Release, September 23, 2026, result family 167, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarUnitDistances.IncidenceEstimates.upper` of [lean/OAI/Geometry/UnitDistances/UnitDistances/RareBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/RareBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarUnitDistances.IncidenceEstimates`, with `open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook`, `open scoped Classical`):
--
--   ```lean
--   theorem upper {C L : ℝ} (hC : 0<C) (hv : R.Valid C L) (hscale : 0<scale s i) :
--       let B := R.book
--       let r := noise s a i
--       B.M ≤ r*B.S ∧ B.WC ≤ (1/a.epsilon)*B.S ∧ B.WB ≤ (r/a.epsilon)*B.S ∧
--       B.HP+B.HQ ≤ BookEnvelope.height C r*B.S ∧
--       B.J ≤ BookEnvelope.j a C (27/50) (1/25) (s.ξ i) r*B.S ∧
--       B.EP ≤ BookEnvelope.pred a r*B.S ∧
--       B.DP ≤ B.CP/20000000+BookEnvelope.star a C r*B.S ∧
--       B.DQ ≤ B.CQ/20000000+BookEnvelope.star a C r*B.S ∧
--       Book.DT (I:=Fin a.k) B ≤ Book.CT (I:=Fin a.k) B/20000000+BookEnvelope.star a C r*B.S ∧
--       B.T ≤ 2*B.HP+BookEnvelope.prediction a r*B.S
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarUnitDistances.ActualScoreBook.ActualBook`, `OAI.PlanarUnitDistances.BookEnvelope.height`, `OAI.PlanarUnitDistances.BookEnvelope.j`, `OAI.PlanarUnitDistances.BookEnvelope.pred`, `OAI.PlanarUnitDistances.BookEnvelope.prediction`, `OAI.PlanarUnitDistances.BookEnvelope.star`, `OAI.PlanarUnitDistances.BudgetParameters.Params`, `OAI.PlanarUnitDistances.FiniteInformation.History`, `OAI.PlanarUnitDistances.FiniteInformation.historyFintype`, `OAI.PlanarUnitDistances.IncidenceBook.Realization`, `OAI.PlanarUnitDistances.IncidenceBook.instFintypeSumSubtypePlaneMemFinsetPQ`, `OAI.PlanarUnitDistances.IncidenceEstimates.instFintypeForallSumSubtypePlaneMemFinsetPQBool`, `OAI.PlanarUnitDistances.IncidenceNoise.noise`, `OAI.PlanarUnitDistances.IncidenceScale.scale`, `OAI.PlanarUnitDistances.IncidenceSequence.Plane`, `OAI.PlanarUnitDistances.IncidenceSequence.Sequence`, `OAI.PlanarUnitDistances.LevelSnapshot.Data`, `OAI.PlanarUnitDistances.IncidenceBook.Realization.Valid`, `OAI.PlanarUnitDistances.IncidenceBook.Realization.book`, `OAI.PlanarUnitDistances.ScoreBook.Book.CP`, `OAI.PlanarUnitDistances.ScoreBook.Book.CQ`, `OAI.PlanarUnitDistances.ScoreBook.Book.CT`, `OAI.PlanarUnitDistances.ScoreBook.Book.DP`, `OAI.PlanarUnitDistances.ScoreBook.Book.DQ`, `OAI.PlanarUnitDistances.ScoreBook.Book.DT`, `OAI.PlanarUnitDistances.ScoreBook.Book.EP`, `OAI.PlanarUnitDistances.ScoreBook.Book.HP`, `OAI.PlanarUnitDistances.ScoreBook.Book.HQ`, `OAI.PlanarUnitDistances.ScoreBook.Book.J`, `OAI.PlanarUnitDistances.ScoreBook.Book.M`, `OAI.PlanarUnitDistances.ScoreBook.Book.S`, `OAI.PlanarUnitDistances.ScoreBook.Book.T`, `OAI.PlanarUnitDistances.ScoreBook.Book.WB` and `OAI.PlanarUnitDistances.ScoreBook.Book.WC` (definitions bundle `OAIQ2Un000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarUnitDistances.IncidenceBand.choose` of this split imports it.
-- source:
--   OpenAI, A power saving for planar unit distances, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/RareBudget.lean (declaration OAI.PlanarUnitDistances.IncidenceEstimates.upper)

import Mathlib
import Definitions.Def_OAIQ2Un000

section

attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceEstimates
open Filter FiniteLaw FiniteStarCoupling RareLabels RareMoments ScoreBook
  IncidenceSequence IncidenceScale IncidenceBook IncidenceNoise ActualScoreBook BudgetParameters
open scoped Classical
noncomputable section
variable {s : Sequence} {a : Params} {i : ℕ}
variable (R : Realization s a i)

attribute [local instance] OAI.PlanarUnitDistances.IncidenceEstimates.instFintypeSumSubtypePlaneMemFinsetPQ
attribute [local instance] OAI.PlanarUnitDistances.IncidenceEstimates.instFintypeForallSumSubtypePlaneMemFinsetPQBool
local instance : Fintype (s.P i×s.Q i) := inferInstance
local instance : Fintype (LevelSnapshot.Data (s.P i⊕s.Q i) (s.P i×s.Q i)) := OAI.PlanarUnitDistances.IncidenceBook.snapshotFintype _ _ _
theorem upper {C L : ℝ} (hC : 0<C) (hv : R.Valid C L) (hscale : 0<scale s i) :
    let B := R.book
    let r := noise s a i
    B.M ≤ r*B.S ∧ B.WC ≤ (1/a.epsilon)*B.S ∧ B.WB ≤ (r/a.epsilon)*B.S ∧
    B.HP+B.HQ ≤ BookEnvelope.height C r*B.S ∧
    B.J ≤ BookEnvelope.j a C (27/50) (1/25) (s.ξ i) r*B.S ∧
    B.EP ≤ BookEnvelope.pred a r*B.S ∧
    B.DP ≤ B.CP/20000000+BookEnvelope.star a C r*B.S ∧
    B.DQ ≤ B.CQ/20000000+BookEnvelope.star a C r*B.S ∧
    Book.DT (I:=Fin a.k) B ≤ Book.CT (I:=Fin a.k) B/20000000+BookEnvelope.star a C r*B.S ∧
    B.T ≤ 2*B.HP+BookEnvelope.prediction a r*B.S := by
  sorry
end
end PlanarUnitDistances.IncidenceEstimates

end OAI
end
