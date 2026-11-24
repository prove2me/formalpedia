-- Prove2me | Theorems.Thm_GlobalTheory_HeisUnit_intInd_diagAt_mul
-- name    : GlobalTheory.HeisUnit.intInd_diagAt_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:18:06.142355+00:00
-- url     : https://prove2.me/theorems/93a8dc03-9aa3-4244-97af-740a959a28fb
-- title:
--   Heis Unit: int Ind diag At mul
-- statement:
--   The Heis Unit construction uses the int Ind diag At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCharacterUnitEqOneHeisenberg.lean#L15-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCharacterUnitEqOneHeisenberg.lean#L15-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntIndMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCharacterUnitEqOneHeisenberg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ValuativeRel
noncomputable section
open GlobalTheory GlobalTheory.HeisUnit
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.HeisUnit.intInd_diagAt_mul {n d : ℕ} {u : kˣ} (hu : valuation k (u : k) = 1) (i0 : Fin n)
    (Y : Matrix (Fin n) (Fin d) k) : intInd k n d ((diagAt u i0).valᵀ * Y) = intInd k n d Y := by sorry
