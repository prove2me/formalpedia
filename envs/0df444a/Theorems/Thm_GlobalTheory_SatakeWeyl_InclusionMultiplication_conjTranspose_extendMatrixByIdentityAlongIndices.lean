-- Prove2me | Theorems.Thm_GlobalTheory_SatakeWeyl_InclusionMultiplication_conjTranspose_extendMatrixByIdentityAlongIndices
-- name    : GlobalTheory.SatakeWeyl.InclusionMultiplication.conjTranspose_extendMatrixByIdentityAlongIndices
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:47:37.505852+00:00
-- url     : https://prove2.me/theorems/c0d3cf64-63f4-482c-94c2-b4504a6552fa
-- title:
--   Inclusion Multiplication: conj Transpose extend Matrix By Identity Along Indices
-- statement:
--   The Inclusion Multiplication construction uses the conj Transpose extend Matrix By Identity Along Indices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallerUnitaryGroupEmbedding.lean#L81-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSmallerUnitaryGroupEmbedding.lean#L81-L92

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

theorem GlobalTheory.SatakeWeyl.InclusionMultiplication.conjTranspose_extendMatrixByIdentityAlongIndices (σ : L →+* L) (e : Fin r → Fin n) (M : Matrix (Fin r) (Fin r) L) :
    cT σ (ext1 e M) = ext1 e (cT σ M) := by sorry
