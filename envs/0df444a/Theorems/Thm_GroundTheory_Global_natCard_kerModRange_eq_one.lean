-- Prove2me | Theorems.Thm_GroundTheory_Global_natCard_kerModRange_eq_one
-- name    : GroundTheory.Global.natCard_kerModRange_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:52.316562+00:00
-- url     : https://prove2.me/theorems/89a6229f-ab45-4c9b-a72e-77d7a9809880
-- title:
--   Global: nat Card ker Mod Range eq one
-- statement:
--   The Global construction uses the nat Card ker Mod Range eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L14-L21

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_CoeGalRootsOfUnityHomApply
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
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
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.ProfCoh
  GroundTheory.GroupCoh
open scoped NumberField.LiesOver ComplexConjugate

theorem GroundTheory.Global.natCard_kerModRange_eq_one {A : Type*} [AddCommGroup A] {f g : A →+ A}
    (h : ∀ x ∈ f.ker, x ∈ g.range) : Nat.card (KerModRange f g) = 1 := by sorry
