-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_ker_proj
-- name    : GroundTheory.LocalField.Abstract.ProfiniteInteger.ker_proj
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:59.61703+00:00
-- url     : https://prove2.me/theorems/38a397dd-1257-464a-a1ac-ab37d826c0ae
-- title:
--   Profinite Integer: ker proj
-- statement:
--   The Profinite Integer construction uses the ker proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ExistsEqNsmulOfProjEqZero.lean#L62-L64

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsEqNsmulOfProjEqZero
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
open GroundTheory.LocalField.Abstract.ProfiniteInteger

theorem GroundTheory.LocalField.Abstract.ProfiniteInteger.ker_proj (n : ℕ+) : (proj n).toAddMonoidHom.ker = multiples n := by sorry
