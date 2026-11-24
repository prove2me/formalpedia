-- Prove2me | Theorems.Thm_GlobalTheory_BorelModulus_coord_conj
-- name    : GlobalTheory.BorelModulus.coord_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:01:48.758274+00:00
-- url     : https://prove2.me/theorems/ebc65961-a462-4112-97a9-5945c467b8f8
-- title:
--   Borel Modulus: coord conj
-- statement:
--   The Borel Modulus construction uses the coord conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousUniMat.lean#L110-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousUniMat.lean#L110-L118

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LineOppositeParabolicUnitaryLeviSectionEq
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsLocallyConstantAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousUniMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Matrix
open scoped NNReal
noncomputable section
open GlobalTheory GlobalTheory.BorelModulus
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem GlobalTheory.BorelModulus.coord_conj (t : Fin n → kˣ) (ht) (x : (borelGL k (Fin n)).U) :
    coord k n (conjAut _ ⟨(borelGL k (Fin n)).s t, ht⟩ x) =
      (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k)).mulVec (coord k n x) := by sorry
