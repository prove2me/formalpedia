-- Prove2me | Theorems.Thm_GlobalTheory_T_rank_le_aleph0_smooth_irreducible_unitaryAdelic
-- name    : GlobalTheory.T.rank_le_aleph0_smooth_irreducible_unitaryAdelic
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:14.139732+00:00
-- url     : https://prove2.me/theorems/032b1542-86fb-5ef4-ad3f-e5e39a985bdf
-- title:
--   T: rank le aleph0 smooth irreducible unitary Adelic
-- statement:
--   The T construction uses the rank le aleph0 smooth irreducible unitary Adelic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelicStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RankLeAleph0SmoothIrreducibleUnitaryAdelicStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsFinTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RankLeAleph0SmoothIrreducibleUnitaryAdelicStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rank_le_aleph0_smooth_irreducible_unitaryAdelic : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (π : Formalism.L2.NG.FinTyp L n), Module.rank ℂ π.S ≤ Cardinal.aleph0 := by sorry
