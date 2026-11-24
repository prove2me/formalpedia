-- Prove2me | Theorems.Thm_GlobalTheory_FinTyp_rank_le_aleph0
-- name    : GlobalTheory.FinTyp.rank_le_aleph0
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:25:58.246705+00:00
-- url     : https://prove2.me/theorems/e4112e2c-32dc-44ab-b469-be1e89f30c1a
-- title:
--   Fin Typ: rank le aleph0
-- statement:
--   The Fin Typ construction uses the rank le aleph0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L167-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelic.lean#L167-L192

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
open GlobalTheory
open GlobalTheory.FinTypCount

theorem GlobalTheory.FinTyp.rank_le_aleph0 : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
    (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by sorry
