-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_incl_mul_apply_of_not
-- name    : GlobalTheory.SatakeWeyl.InclusionMultiplication.incl_mul_apply_of_not
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:07.598277+00:00
-- url     : https://prove2.me/theorems/f7d03a05-47ee-4749-91d6-3954456e3d4f
-- title:
--   Inclusion Multiplication: incl mul apply of not
-- statement:
--   The Inclusion Multiplication construction uses the incl mul apply of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallerUnitaryGroupEmbedding.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallerUnitaryGroupEmbedding.lean#L19-L24

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

theorem GlobalTheory.SatakeWeyl.InclusionMultiplication.incl_mul_apply_of_not {p : Type} {e : Fin r → Fin n} (M : Matrix (Fin r) p L)
    {a : Fin n} (ha : a ∉ Set.range e) (j : p) : (incl L e * M) a j = 0 := by sorry
