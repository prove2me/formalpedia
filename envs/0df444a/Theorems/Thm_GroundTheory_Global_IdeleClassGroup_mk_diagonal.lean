-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleClassGroup_mk_diagonal
-- name    : GroundTheory.Global.IdeleClassGroup.mk_diagonal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:32.581057+00:00
-- url     : https://prove2.me/theorems/83f5ca14-676d-421e-89e1-eed7121c7c7b
-- title:
--   Idele Class Group: mk diagonal
-- statement:
--   The Idele Class Group construction uses the mk diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L81-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/InfiniteProjInfiniteEmbeddingOfNe.lean#L81-L82

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_InfiniteProjInfiniteEmbeddingOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing RestrictedProduct
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
open GroundTheory.Global.IdeleClassGroup

theorem GroundTheory.Global.IdeleClassGroup.mk_diagonal (x : Kˣ) : mk K (IdeleGroup.diagonal K x) = 1 := by sorry
