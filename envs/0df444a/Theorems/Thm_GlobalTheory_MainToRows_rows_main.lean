-- Prove2me | Theorems.Thm_GlobalTheory_MainToRows_rows_main
-- name    : GlobalTheory.MainToRows.rows_main
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:11.460387+00:00
-- url     : https://prove2.me/theorems/23d11faa-292f-4728-b59d-3d4220c6e7a7
-- title:
--   Main To Rows: rows main
-- statement:
--   The Main To Rows construction uses the rows main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MainTermImpliesRowHypothesis.lean#L131-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MainTermImpliesRowHypothesis.lean#L131-L139

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open GlobalTheory GlobalTheory.MainToRows
variable {C : Type} [Field C]

theorem GlobalTheory.MainToRows.rows_main (V : VF C) (i n0 : ℕ) :
    ∑ ρ : Fin n0, rename (rowE ρ) (mainM V i (fun b c : Fin n0 => if b = c then (-1 : C) else 0)) =
      -((V.l : C) ^ (expE V.l i))⁻¹ • (∑ b : Fin n0, ∑ c : Fin n0,
        (X (Sum.inl (b, c)) ^ (V.l ^ i) * X (Sum.inr (b, c)) : MvPowerSeries (PVar n0) C)) := by sorry
