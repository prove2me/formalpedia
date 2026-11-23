-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_unitsRep_toMul
-- name    : GroundTheory.Global.InfinitePlace.unitsRep_toMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:23.508743+00:00
-- url     : https://prove2.me/theorems/bd292f3b-5a19-404b-b7ea-0191fe46e2cc
-- title:
--   Infinite Place: units Rep to Mul
-- statement:
--   The Infinite Place construction uses the units Rep to Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L292-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L292-L294

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

theorem GroundTheory.Global.InfinitePlace.unitsRep_toMul (σ : Gal(w.Completion/v.Completion)) (x : Additive w.Completionˣ) :
    ((unitsRep v w σ x).toMul : w.Completion) = σ (x.toMul : w.Completion) := by sorry
