-- Prove2me | Theorems.Thm_OAI_BinaryCoordinateSweeps_GridSplit_occurring_auxiliary_eventually
-- name    : OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T15:58:06.82528+00:00
-- url     : https://prove2.me/theorems/9c87da9b-30f1-4077-8ba5-bdc656a88e83
-- title:
--   OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually: intermediate lemma from OpenAI, Row–column symmetry and contraction of coordinate sweeps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.binary_sweep_contraction_and_mixing`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Row–column symmetry and contraction of coordinate sweeps*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually` of [lean/OAI/Probability/BinarySweep/YoungTheory/GenericHookAux.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BinarySweep/YoungTheory/GenericHookAux.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinaryCoordinateSweeps.GridSplit`, with `open scoped BigOperators Classical`, `open Filter`, `open Irrep Representation Signed`):
--
--   ```lean
--   theorem occurring_auxiliary_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
--       ∀ m n h : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
--       gridSize bits=s →
--       1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
--       Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
--       Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
--       ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
--       ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
--       ∀ (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V) [ρ.IsIrreducible],
--       (∀g v, ‖ρ g v‖=‖v‖) →
--       0<Module.finrank ℂ (IntertwiningMap ρ
--         (hilbertTensorRep (Prod.fst : Bool × Fin t → Bool) (junctionSize bits H))) → ∀z : ℝ,
--       (∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
--         evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
--           Real.exp (-cExponent (gridSize (leftBits bits))*typeF a.val+
--             eExponent (gridSize (leftBits bits))*Fintype.card (RowLabels bits H y)*
--             Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) →
--       (∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
--         evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
--           Real.exp (-cExponent (gridSize (rightBits bits))*typeF a.val+
--             eExponent (gridSize (rightBits bits))*Fintype.card (ColumnLabels bits H x)*
--             Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) →
--       evenMoment q (groupAverage (ρ.comp
--         (inputToJunction bits H).permCongrHom.toMonoidHom)
--         (fun a => (conditionalGroupLaw H z a:ℂ)))≤
--         Real.exp (-(cExponent s+inductionGap s)*Real.log (Module.finrank ℂ V:ℝ)+
--           (eExponent s-inductionGap s)*h*Real.log s-pathCost H+(s:ℝ)^(9/10:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinaryCoordinateSweeps.FreeSlot`, `OAI.BinaryCoordinateSweeps.GridSlot`, `OAI.BinaryCoordinateSweeps.PathFamily`, `OAI.BinaryCoordinateSweeps.cExponent`, `OAI.BinaryCoordinateSweeps.conditionalGroupLaw`, `OAI.BinaryCoordinateSweeps.eExponent`, `OAI.BinaryCoordinateSweeps.freeSlotFintype`, `OAI.BinaryCoordinateSweeps.gridSize`, `OAI.BinaryCoordinateSweeps.inductionGap`, `OAI.BinaryCoordinateSweeps.pathCost`, `OAI.BinaryCoordinateSweeps.GridSplit.ColumnLabels`, `OAI.BinaryCoordinateSweeps.GridSplit.RowLabels`, `OAI.BinaryCoordinateSweeps.GridSplit.columnChildWeight`, `OAI.BinaryCoordinateSweeps.GridSplit.columnFamily`, `OAI.BinaryCoordinateSweeps.GridSplit.columnFreeSize`, `OAI.BinaryCoordinateSweeps.GridSplit.columnLabelsFintype`, `OAI.BinaryCoordinateSweeps.GridSplit.inputToJunction`, `OAI.BinaryCoordinateSweeps.GridSplit.junctionSize`, `OAI.BinaryCoordinateSweeps.GridSplit.leftBits`, `OAI.BinaryCoordinateSweeps.GridSplit.rightBits`, `OAI.BinaryCoordinateSweeps.GridSplit.rowChildWeight`, `OAI.BinaryCoordinateSweeps.GridSplit.rowFamily`, `OAI.BinaryCoordinateSweeps.GridSplit.rowFreeSize`, `OAI.BinaryCoordinateSweeps.GridSplit.rowLabelsFintype`, `OAI.BinaryCoordinateSweeps.Irrep.evenMoment`, `OAI.BinaryCoordinateSweeps.Irrep.groupAverage`, `OAI.BinaryCoordinateSweeps.Signed.ActiveType`, `OAI.BinaryCoordinateSweeps.Signed.TensorSpace`, `OAI.BinaryCoordinateSweeps.Signed.hilbertTensorRep`, `OAI.BinaryCoordinateSweeps.Signed.typeF`, `OAI.BinaryCoordinateSweeps.Signed.typeProjection`, `OAI.BinaryCoordinateSweeps.Young.Cell`, `OAI.BinaryCoordinateSweeps.Young.PartitionHilbert`, `OAI.BinaryCoordinateSweeps.Young.Tabloid`, `OAI.BinaryCoordinateSweeps.Young.diagram`, `OAI.BinaryCoordinateSweeps.Young.hilbertInner`, `OAI.BinaryCoordinateSweeps.Young.hilbertNormed`, `OAI.BinaryCoordinateSweeps.Young.instFintypeElemForallCellNatTabloid` and `OAI.BinaryCoordinateSweeps.Young.partitionHilbertRep` (definitions bundle `OAIB3Bs000` of this split); `OAI.BinaryCoordinateSweeps.Slot` (the published bundle `Def_BinarySweep`).
--
--   **Used by.** The proof of `OAI.BinaryCoordinateSweeps.dense_induction_step_eventually` of this split imports it.
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BinarySweep/YoungTheory/GenericHookAux.lean (declaration OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually)

import Mathlib
import Definitions.Def_BinarySweep
import Definitions.Def_OAIB3Bs000

section

attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.Young.diagonalStabilizer_fintype _root_.OAI.BinaryCoordinateSweeps.Young.signTwist_irreducible _root_.OAI.BinaryCoordinateSweeps.finitePathFamily _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped BigOperators Classical
open Filter

namespace BinaryCoordinateSweeps.GridSplit
open Irrep Representation Signed

variable {m n h : ℕ} (bits : Fin (m+n) → ℕ) (H : PathFamily bits h)

theorem occurring_auxiliary_eventually (q : ℕ) (hq : 2≤q) : ∀ᶠ s : ℕ in atTop,
    ∀ m n h : ℕ, ∀ bits : Fin (m+n) → ℕ, ∀ H : PathFamily bits h,
    gridSize bits=s →
    1≤Real.log (gridSize (leftBits bits)) → 1≤Real.log (gridSize (rightBits bits)) →
    Real.log (gridSize (leftBits bits))≤(4/5:ℝ)*Real.log s →
    Real.log (gridSize (rightBits bits))≤(4/5:ℝ)*Real.log s →
    ∀ t : ℕ, 0<t → (t:ℝ)≤(s:ℝ)^(1/100:ℝ) →
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
    ∀ (ρ : Representation ℂ (Equiv.Perm (Fin (junctionSize bits H))) V) [ρ.IsIrreducible],
    (∀g v, ‖ρ g v‖=‖v‖) →
    0<Module.finrank ℂ (IntertwiningMap ρ
      (hilbertTensorRep (Prod.fst : Bool × Fin t → Bool) (junctionSize bits H))) → ∀z : ℝ,
    (∀y (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (rowFreeSize bits H y)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (rowChildWeight bits H z y))≤
        Real.exp (-cExponent (gridSize (leftBits bits))*typeF a.val+
          eExponent (gridSize (leftBits bits))*Fintype.card (RowLabels bits H y)*
          Real.log (gridSize (leftBits bits))-pathCost (rowFamily bits H y))) →
    (∀x (a : ActiveType (Prod.fst : Bool × Fin t → Bool) (columnFreeSize bits H x)),
      evenMoment q (groupAverage (Young.partitionHilbertRep a.val) (columnChildWeight bits H z x))≤
        Real.exp (-cExponent (gridSize (rightBits bits))*typeF a.val+
          eExponent (gridSize (rightBits bits))*Fintype.card (ColumnLabels bits H x)*
          Real.log (gridSize (rightBits bits))-pathCost (columnFamily bits H x))) →
    evenMoment q (groupAverage (ρ.comp
      (inputToJunction bits H).permCongrHom.toMonoidHom)
      (fun a => (conditionalGroupLaw H z a:ℂ)))≤
      Real.exp (-(cExponent s+inductionGap s)*Real.log (Module.finrank ℂ V:ℝ)+
        (eExponent s-inductionGap s)*h*Real.log s-pathCost H+(s:ℝ)^(9/10:ℝ)) := by
  sorry

end BinaryCoordinateSweeps.GridSplit

end

open scoped BigOperators Classical
open Filter

end

end OAI
end
