-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_dvd_of_intCast_eq_nsmul
-- name    : GroundTheory.LocalField.Abstract.ProfiniteInteger.dvd_of_intCast_eq_nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:56.102486+00:00
-- url     : https://prove2.me/theorems/fd61b6ef-eff8-4f37-b768-e1cb644d045f
-- title:
--   Profinite Integer: dvd of int Cast eq nsmul
-- statement:
--   The Profinite Integer construction uses the dvd of int Cast eq nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean#L57-L62

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
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

theorem GroundTheory.LocalField.Abstract.ProfiniteInteger.dvd_of_intCast_eq_nsmul {n : ℕ} (hn : 0 < n) {m : ℤ} {w : ℤ̂} (h : (m : ℤ̂) = n • w) :
    (n : ℤ) ∣ m := by sorry
