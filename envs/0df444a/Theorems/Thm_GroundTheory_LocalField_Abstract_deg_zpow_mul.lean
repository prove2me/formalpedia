-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_deg_zpow_mul
-- name    : GroundTheory.LocalField.Abstract.deg_zpow_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:11:13.473169+00:00
-- url     : https://prove2.me/theorems/5162ace5-fcd0-44af-88fe-6c585cccea0d
-- title:
--   Abstract: deg zpow mul
-- statement:
--   The Abstract construction uses the deg zpow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L62-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/Frobenius.lean#L62-L68

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Valuation
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Frobenius
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}

theorem GroundTheory.LocalField.Abstract.deg_zpow_mul {N : ℕ} (hdσ : d σ = Multiplicative.ofAdd (N : ℤ̂)) (k : ℤ) {j : G}
    (hj : j ∈ L ⊓ d.ker) :
    Multiplicative.toAdd (d (σ ^ k * j)) = ((k * N : ℤ) : ℤ̂) := by sorry
