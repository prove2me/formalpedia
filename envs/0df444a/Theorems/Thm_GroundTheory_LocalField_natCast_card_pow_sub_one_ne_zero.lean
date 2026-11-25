-- Prove2me | Theorems.Thm_GroundTheory_LocalField_natCast_card_pow_sub_one_ne_zero
-- name    : GroundTheory.LocalField.natCast_card_pow_sub_one_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:41:05.479829+00:00
-- url     : https://prove2.me/theorems/2cb56d8c-ebb4-4d5e-bb0d-d569b7e0932d
-- title:
--   Local Field: nat Cast card pow sub one ne zero
-- statement:
--   The Local Field construction uses the nat Cast card pow sub one ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L237-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L237-L242

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)
variable {K L}

theorem GroundTheory.LocalField.natCast_card_pow_sub_one_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ((Nat.card 𝓀[K] ^ n - 1 : ℕ) : 𝓀[K]) ≠ 0 := by sorry
