-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_antiJ_apply
-- name    : GlobalTheory.SatakeWeyl.InclusionMultiplication.antiJ_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:48:20.683829+00:00
-- url     : https://prove2.me/theorems/c3d28997-d127-4fb3-bced-0b4f3461f47b
-- title:
--   Inclusion Multiplication: anti J apply
-- statement:
--   The Inclusion Multiplication construction uses the anti J apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallerUnitaryGroupEmbedding.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallerUnitaryGroupEmbedding.lean#L41-L45

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSmallerUnitaryGroupEmbedding
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open Matrix
open GlobalTheory GlobalTheory.SatakeWeyl GlobalTheory.SatakeWeyl.InclusionMultiplication
variable {L : Type} [Field L] {n r : ℕ}

theorem GlobalTheory.SatakeWeyl.InclusionMultiplication.antiJ_apply (i j : Fin n) : antiJ L n i j = if i.rev = j then 1 else 0 := by sorry
