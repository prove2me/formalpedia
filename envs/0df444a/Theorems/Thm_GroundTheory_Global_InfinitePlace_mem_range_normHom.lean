-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_mem_range_normHom
-- name    : GroundTheory.Global.InfinitePlace.mem_range_normHom
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:21.602793+00:00
-- url     : https://prove2.me/theorems/6798847f-5273-415f-8bb7-7c3f83639c4e
-- title:
--   Infinite Place: mem range norm Hom
-- statement:
--   The Infinite Place construction uses the mem range norm Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L319-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L319-L340

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

theorem GroundTheory.Global.InfinitePlace.mem_range_normHom (hv : v.IsReal) (hw : w.IsComplex) (x : Additive w.Completionˣ)
    (hx : completionConj (w := w) hv (x.toMul : w.Completion) = x.toMul)
    (hpos : 0 < (extensionEmbedding w (x.toMul : w.Completion)).re) :
    x ∈ (normHom (unitsRep v w)).range := by sorry
