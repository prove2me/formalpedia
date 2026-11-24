-- Prove2me | Theorems.Thm_GlobalTheory_FinTypCount_exists_denom_matrix
-- name    : GlobalTheory.FinTypCount.exists_denom_matrix
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:25:38.00398+00:00
-- url     : https://prove2.me/theorems/3b13820c-6a50-4808-9a19-4d9a47658752
-- title:
--   Fin Typ Count: exists denom matrix
-- statement:
--   The Fin Typ Count construction uses the exists denom matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L64-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L64-L71

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

theorem GlobalTheory.FinTypCount.exists_denom_matrix (G : Matrix (Fin n) (Fin n) (AL L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, (m : AL L) * G i j ∈ ALint L := by sorry
