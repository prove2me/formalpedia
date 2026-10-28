-- Prove2me | Theorems.Thm_OAI_BinaryCoordinateSweeps_Signed_actual_board_overlap_exp
-- name    : OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T15:58:03.720472+00:00
-- url     : https://prove2.me/theorems/6460c0d9-eab6-4463-a77b-a14c7008233b
-- title:
--   OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp: intermediate lemma from OpenAI, Row–column symmetry and contraction of coordinate sweeps
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.binary_sweep_contraction_and_mixing`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Row–column symmetry and contraction of coordinate sweeps*, OpenAI Math Release, September 26, 2026, result family 238, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp` of [lean/OAI/Probability/BinarySweep/GridBounds/GroupedLogBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BinarySweep/GridBounds/GroupedLogBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.BinaryCoordinateSweeps.Signed`, with `open scoped BigOperators Classical MonoidAlgebra ComplexOrder Matrix.Norms.L2Operator`, `open Matrix`, `open Density Irrep Representation TraceHolder`):
--
--   ```lean
--   theorem actual_board_overlap_exp
--       [Nonempty A] [Nonempty I]
--       {J W : Type*} [Fintype J] [LinearOrder J]
--       {m : J → ℕ} {U : J → Type*} [∀j,NormedAddCommGroup (U j)]
--       [∀j,InnerProductSpace ℂ (U j)] [∀j,FiniteDimensional ℂ (U j)]
--       [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
--       (board : Fin N ↪ I × J) (p : A → Bool)
--       (eR : (Σₗ i, Fin (n i)) ≃o Fin N) (eC : (Σₗ j, Fin (m j)) ≃o Fin N)
--       (gR gC : Equiv.Perm (Fin N))
--       (hR : ∀t, groupOf eR gR t=(board t).1) (hC : ∀t, groupOf eC gC t=(board t).2)
--       (ρ : Representation ℂ (Equiv.Perm (Fin N)) W) [ρ.IsIrreducible]
--       (α : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) [∀i, (α i).IsIrreducible]
--       (β : ∀j, Representation ℂ (Equiv.Perm (Fin (m j))) (U j)) [∀j, (β j).IsIrreducible] :
--       ‖groupedProjection eC gC p β*isotypicProjection p ρ*groupedProjection eR gR p α‖^2 ≤
--         Real.exp ((∑i, Real.log (Module.finrank ℂ (V i):ℝ))+
--           (∑j, Real.log (Module.finrank ℂ (U j):ℝ))-Real.log (Module.finrank ℂ W:ℝ)+
--           (Fintype.card I*Fintype.card J-(N:ℝ))+
--           4*(Fintype.card A:ℝ)^2*((∑i, Real.log (n i+1:ℝ))+(∑j, Real.log (m j+1:ℝ))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.BinaryCoordinateSweeps.Signed.groupOf`, `OAI.BinaryCoordinateSweeps.Signed.groupedProjection` and `OAI.BinaryCoordinateSweeps.Signed.isotypicProjection` (definitions bundle `OAIB3Bs000` of this split).
--
--   **Used by.** The proof of `OAI.BinaryCoordinateSweeps.GridSplit.occurring_auxiliary_eventually` of this split imports it.
-- source:
--   OpenAI, Row–column symmetry and contraction of coordinate sweeps, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 238; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Row-column-symmetry-and-contraction-of-coordinate-sweeps-September-26-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/BinarySweep/GridBounds/GroupedLogBounds.lean (declaration OAI.BinaryCoordinateSweeps.Signed.actual_board_overlap_exp)

import Mathlib
import Definitions.Def_OAIB3Bs000

section

attribute [-instance] _root_.OAI.BinaryCoordinateSweeps.oneAxisOutsideEmpty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical MonoidAlgebra ComplexOrder Matrix.Norms.L2Operator
open Matrix

namespace BinaryCoordinateSweeps.Signed
open Density Irrep Representation TraceHolder

variable {A I : Type*} [Fintype A] [DecidableEq A] [Fintype I] [LinearOrder I]
  {n : I → ℕ} {N : ℕ}
  {V : I → Type*} [∀i, NormedAddCommGroup (V i)]
  [∀i, InnerProductSpace ℂ (V i)] [∀i, FiniteDimensional ℂ (V i)]

theorem actual_board_overlap_exp
    [Nonempty A] [Nonempty I]
    {J W : Type*} [Fintype J] [LinearOrder J]
    {m : J → ℕ} {U : J → Type*} [∀j,NormedAddCommGroup (U j)]
    [∀j,InnerProductSpace ℂ (U j)] [∀j,FiniteDimensional ℂ (U j)]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (board : Fin N ↪ I × J) (p : A → Bool)
    (eR : (Σₗ i, Fin (n i)) ≃o Fin N) (eC : (Σₗ j, Fin (m j)) ≃o Fin N)
    (gR gC : Equiv.Perm (Fin N))
    (hR : ∀t, groupOf eR gR t=(board t).1) (hC : ∀t, groupOf eC gC t=(board t).2)
    (ρ : Representation ℂ (Equiv.Perm (Fin N)) W) [ρ.IsIrreducible]
    (α : ∀i, Representation ℂ (Equiv.Perm (Fin (n i))) (V i)) [∀i, (α i).IsIrreducible]
    (β : ∀j, Representation ℂ (Equiv.Perm (Fin (m j))) (U j)) [∀j, (β j).IsIrreducible] :
    ‖groupedProjection eC gC p β*isotypicProjection p ρ*groupedProjection eR gR p α‖^2 ≤
      Real.exp ((∑i, Real.log (Module.finrank ℂ (V i):ℝ))+
        (∑j, Real.log (Module.finrank ℂ (U j):ℝ))-Real.log (Module.finrank ℂ W:ℝ)+
        (Fintype.card I*Fintype.card J-(N:ℝ))+
        4*(Fintype.card A:ℝ)^2*((∑i, Real.log (n i+1:ℝ))+(∑j, Real.log (m j+1:ℝ)))) := by
  sorry

end BinaryCoordinateSweeps.Signed

end

end OAI
end
