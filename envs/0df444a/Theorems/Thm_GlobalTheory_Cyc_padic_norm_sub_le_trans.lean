-- Prove2me | Theorems.Thm_GlobalTheory_Cyc_padic_norm_sub_le_trans
-- name    : GlobalTheory.Cyc.padic_norm_sub_le_trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:04.11383+00:00
-- url     : https://prove2.me/theorems/e995a364-2e1f-49ff-bdab-a51d517dde45
-- title:
--   Cyc: padic norm sub le trans
-- statement:
--   The Cyc construction uses the padic norm sub le trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CyclotomicCharacterPadicBasicProperties.lean#L16-L20

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc
variable {l : ℕ} [Fact l.Prime]

theorem GlobalTheory.Cyc.padic_norm_sub_le_trans {x y z : ℚ_[l]} {r : ℝ} (h1 : ‖x - y‖ ≤ r) (h2 : ‖y - z‖ ≤ r) :
    ‖x - z‖ ≤ r := by sorry
