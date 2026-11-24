-- Prove2me | Theorems.Thm_GlobalTheory_T_localization_maximal_ideal_map
-- name    : GlobalTheory.T.localization_maximal_ideal_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T20:52:30.816469+00:00
-- url     : https://prove2.me/theorems/1168a781-1f44-4e24-b8d1-8e587e512992
-- title:
--   T: localization maximal ideal map
-- statement:
--   The T construction uses the localization maximal ideal map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationMaximalIdealMapStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationMaximalIdealMapStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationMaximalIdealMap
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationMaximalIdealMapStatement
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

theorem GlobalTheory.T.localization_maximal_ideal_map : ∀ (B S : Type) [CommRing B] [IsLocalRing B] [CommRing S] [Algebra B S] (J q : Ideal S) [q.IsMaximal], J ≤ (IsLocalRing.maximalIdeal B).map (algebraMap B S) → (IsLocalRing.maximalIdeal B).map (algebraMap B S) ≤ q → Algebra.FormallyUnramified B (S ⧸ J) → Module.Finite B (S ⧸ J) → (IsLocalRing.maximalIdeal B).map ((algebraMap S (Localization.AtPrime q)).comp (algebraMap B S)) = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by sorry
