-- Prove2me | Theorems.Thm_GroundTheory_LocalField_StableFiltration_smul_grMk
-- name    : GroundTheory.LocalField.StableFiltration.smul_grMk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:04.844195+00:00
-- url     : https://prove2.me/theorems/99d3ed02-7d4a-453f-9368-7c8544f5b8bd
-- title:
--   Stable Filtration: smul gr Mk
-- statement:
--   The Stable Filtration construction uses the smul gr Mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L150-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivial.lean#L150-L150

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset Filter
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)

theorem GroundTheory.LocalField.StableFiltration.smul_grMk {n : ℕ} (g : G) (x : S.F n) : g • S.grMk n x = S.grMk n (g • x) := by sorry
