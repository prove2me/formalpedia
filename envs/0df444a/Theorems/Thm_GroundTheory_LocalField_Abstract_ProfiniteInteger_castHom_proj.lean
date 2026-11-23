-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_castHom_proj
-- name    : GroundTheory.LocalField.Abstract.ProfiniteInteger.castHom_proj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:59.841788+00:00
-- url     : https://prove2.me/theorems/1c5aeb76-4452-4779-8a02-4202a77ae868
-- title:
--   Profinite Integer: cast Hom proj
-- statement:
--   The Profinite Integer construction uses the cast Hom proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/AbstractLocalReciprocity/ProfiniteInteger.lean#L26-L28

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

theorem GroundTheory.LocalField.Abstract.ProfiniteInteger.castHom_proj {m n : ℕ+} (h : (m : ℕ) ∣ n) (x : ℤ̂) :
    ZMod.castHom h (ZMod m) (proj n x) = proj m x := by sorry
