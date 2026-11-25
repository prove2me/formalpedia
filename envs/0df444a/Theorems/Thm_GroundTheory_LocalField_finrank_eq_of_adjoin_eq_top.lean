-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finrank_eq_of_adjoin_eq_top
-- name    : GroundTheory.LocalField.finrank_eq_of_adjoin_eq_top
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:14:49.120617+00:00
-- url     : https://prove2.me/theorems/80ebbf39-2eab-4960-9ea0-d26cce7c29ce
-- title:
--   Local Field: finrank eq of adjoin eq top
-- statement:
--   The Local Field construction uses the finrank eq of adjoin eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L244-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedGalois.lean#L244-L289

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

theorem GroundTheory.LocalField.finrank_eq_of_adjoin_eq_top {n : ℕ} (hn : n ≠ 0) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (Nat.card 𝓀[K] ^ n - 1)) (htop : K⟮ζ⟯ = ⊤) :
    Module.finrank K L = n := by sorry
