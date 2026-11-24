-- Prove2me | Theorems.Thm_GlobalTheory_T_localization_residue_finite_unram
-- name    : GlobalTheory.T.localization_residue_finite_unram
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:53.792835+00:00
-- url     : https://prove2.me/theorems/e28f3afb-f21d-4e50-9be3-c3a5eac7f3a8
-- title:
--   T: localization residue finite unram
-- statement:
--   The T construction uses the localization residue finite unram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationResidueFiniteUnramStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationResidueFiniteUnramStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationResidueFiniteUnram
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationResidueFiniteUnramStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.localization_residue_finite_unram : ∀ (B S : Type) [CommRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).Finite ∧ ((IsLocalRing.residue (Localization.AtPrime q)).comp ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S))).FormallyUnramified := by sorry
