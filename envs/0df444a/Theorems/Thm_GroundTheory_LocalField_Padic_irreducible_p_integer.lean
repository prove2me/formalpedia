-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_irreducible_p_integer
-- name    : GroundTheory.LocalField.Padic.irreducible_p_integer
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:16.973726+00:00
-- url     : https://prove2.me/theorems/a190e664-36aa-5fbc-aec9-8b6608350871
-- title:
--   Padic: irreducible p integer
-- statement:
--   The Padic construction uses the irreducible p integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L44-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L44-L47

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
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
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]

theorem GroundTheory.LocalField.Padic.irreducible_p_integer : Irreducible (p : 𝒪[ℚ_[p]]) := by sorry
