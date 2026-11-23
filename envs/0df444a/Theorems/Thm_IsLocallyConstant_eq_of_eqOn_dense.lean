-- Prove2me | Theorems.Thm_IsLocallyConstant_eq_of_eqOn_dense
-- name    : IsLocallyConstant.eq_of_eqOn_dense
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:11.209165+00:00
-- url     : https://prove2.me/theorems/431ba9a7-cef9-4ee9-a89c-e0ef30ae4f98
-- title:
--   Is Locally Constant: eq of eq On dense
-- statement:
--   The Is Locally Constant construction uses the eq of eq On dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ProcyclicDefs.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ProcyclicDefs.lean#L18-L23

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
variable {G : Type*} [Group G] [TopologicalSpace G]

theorem IsLocallyConstant.eq_of_eqOn_dense {X Y : Type*} [TopologicalSpace X] {f g : X → Y}
    (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) {s : Set X} (hs : Dense s)
    (h : Set.EqOn f g s) : f = g := by sorry
