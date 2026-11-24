-- Prove2me | Theorems.Thm_GlobalTheory_FinTypCount_countable_range_rt
-- name    : GlobalTheory.FinTypCount.countable_range_rt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:59.879133+00:00
-- url     : https://prove2.me/theorems/7ef64d97-0892-40e5-99e5-cb44d8ceee82
-- title:
--   Fin Typ Count: countable range rt
-- statement:
--   The Fin Typ Count construction uses the countable range rt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L139-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L139-L159

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

theorem GlobalTheory.FinTypCount.countable_range_rt {f : GAf L n → ℂ} {N : ℕ} (hN : 0 < N)
    (hf : ∀ κ, Cong L n N κ → rt L n κ f = f) :
    (Set.range fun h : GAf L n => rt L n h f).Countable := by sorry
