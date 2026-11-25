-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_cyclicHerbrand_unitsRep_eq_finrank
-- name    : GroundTheory.Global.InfinitePlace.cyclicHerbrand_unitsRep_eq_finrank
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:01.434824+00:00
-- url     : https://prove2.me/theorems/152c198d-3b5e-4876-95c5-0141af525364
-- title:
--   Infinite Place: cyclic Herbrand units Rep eq finrank
-- statement:
--   The Infinite Place construction uses the cyclic Herbrand units Rep eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L434-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L434-L457

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
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {v : InfinitePlace K}
  (w : InfinitePlace L) [w.LiesOver v]
variable (v)
variable {v w}
variable (v w)

theorem GroundTheory.Global.InfinitePlace.cyclicHerbrand_unitsRep_eq_finrank (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cyclicHerbrand (unitsRep v w) σ = Module.finrank v.Completion w.Completion := by sorry
