-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateCohomologyZeroIso_inv_mk
-- name    : GroundTheory.GroupCoh.tateCohomologyZeroIso_inv_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:25.467141+00:00
-- url     : https://prove2.me/theorems/d3e09559-4ffd-4ec3-86d0-2f97c020b3d0
-- title:
--   Group Coh: tate Cohomology Zero Iso inv mk
-- statement:
--   The Group Coh construction uses the tate Cohomology Zero Iso inv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L224-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateLow.lean#L224-L230

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ModuleHomologyData
import Definitions.Def_GroundTheory_TateCohomology_TateLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Representation groupCohomology groupHomology
universe u
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.tateCohomologyZeroIso_inv_mk (M : Rep.{u} R G) (z : (tateComplex M).cycles 0)
    (x : M.ρ.invariants) (hx : (cochainsIso₀ M).inv.hom x = ((tateComplex M).iCycles 0).hom z) :
    ((tateCohomologyZeroIso R G).app M).inv.hom (Submodule.Quotient.mk x) =
      ((tateComplex M).homologyπ 0).hom z := by sorry
