-- Prove2me | Theorems.Thm_GlobalTheory_BorelUMod_conj_mem_iff
-- name    : GlobalTheory.BorelUMod.conj_mem_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:18.909417+00:00
-- url     : https://prove2.me/theorems/91d92d44-8295-41d4-87ad-bd15a72d2d89
-- title:
--   Borel UMod: conj mem iff
-- statement:
--   The Borel UMod construction uses the conj mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealWeight.lean#L53-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealWeight.lean#L53-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_RelIndexMulMeasure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemGUIffAdjJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexEqOfSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexUpLatEqProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnipLatIsOpenIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ImportsTerTail
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealWeight
import Theorems.Thm_GlobalTheory_BorelUMod_isWeight_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Formalism.UG
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelUMod
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ}

theorem GlobalTheory.BorelUMod.conj_mem_iff {σ : L →+* L} [LocallyCompactSpace (GU σ n)] (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (t : torusU σ n) (u : (borelU σ n).U) :
    conjAut (borelU σ n).U ⟨(borelU σ n).s t, (borelU σ n).Q_le_normalizer ((borelU σ n).s_mem _)⟩ u ∈
      unipLat hσ (isWeight_ord hσ t) ↔ u ∈ unipLat hσ isWeight_zero := by sorry
