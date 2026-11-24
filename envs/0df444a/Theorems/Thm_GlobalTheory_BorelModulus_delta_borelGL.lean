-- Prove2me | Theorems.Thm_GlobalTheory_BorelModulus_delta_borelGL
-- name    : GlobalTheory.BorelModulus.delta_borelGL
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:01:56.526346+00:00
-- url     : https://prove2.me/theorems/9f576977-551d-4e80-be26-74f2d937d0c6
-- title:
--   Borel Modulus: delta borel GL
-- statement:
--   The Borel Modulus construction uses the delta borel GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousUniMat.lean#L187-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousUniMat.lean#L187-L197

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

theorem GlobalTheory.BorelModulus.delta_borelGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (q : (borelGL k (Fin n)).Q), (((borelGL k (Fin n)).delta q : ℝ≥0) : ℝ) =
      ∏ i : Fin n, GlobalTheory.SplitWeil.nabs k ((borelGL k (Fin n)).p q i) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)) := by sorry
