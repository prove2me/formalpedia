-- Prove2me | Theorems.Thm_GlobalTheory_FinTypCount_inv_val
-- name    : GlobalTheory.FinTypCount.inv_val
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:48.658551+00:00
-- url     : https://prove2.me/theorems/e75bf8fb-c3a7-449b-be21-396e9f332505
-- title:
--   Fin Typ Count: inv val
-- statement:
--   The Fin Typ Count construction uses the inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L83-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L83-L88

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FiniteAdeleStrongApproximationModNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2.NG
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.FinTypCount
variable {L : Type} [Field L] [NumberField L] [IsCMField L]
local notation3 "L⁺" => NumberField.maximalRealSubfield L
variable {n : ℕ}

theorem GlobalTheory.FinTypCount.inv_val (g : GAf L n) :
    (((g⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      conjT (conjAL L) (g.1 : Matrix (Fin n) (Fin n) (AL L)) := by sorry
