-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_normHom_unitsRep_toMul
-- name    : GroundTheory.Global.InfinitePlace.normHom_unitsRep_toMul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:07.812682+00:00
-- url     : https://prove2.me/theorems/675609e3-e1b3-4fcd-9ec7-052981a23a77
-- title:
--   Infinite Place: norm Hom units Rep to Mul
-- statement:
--   The Infinite Place construction uses the norm Hom units Rep to Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L303-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L303-L309

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

theorem GroundTheory.Global.InfinitePlace.normHom_unitsRep_toMul (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ) :
    ((normHom (unitsRep v w) x).toMul : w.Completion) =
      (x.toMul : w.Completion) * completionConj (w := w) hv (x.toMul : w.Completion) := by sorry
