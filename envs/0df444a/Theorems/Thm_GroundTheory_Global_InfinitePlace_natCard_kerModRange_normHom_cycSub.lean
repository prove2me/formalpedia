-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_natCard_kerModRange_normHom_cycSub
-- name    : GroundTheory.Global.InfinitePlace.natCard_kerModRange_normHom_cycSub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:35.997738+00:00
-- url     : https://prove2.me/theorems/c8abdc31-733a-40e4-8ae4-76dc60240071
-- title:
--   Infinite Place: nat Card ker Mod Range norm Hom cyc Sub
-- statement:
--   The Infinite Place construction uses the nat Card ker Mod Range norm Hom cyc Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L404-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/InfiniteNormIndex/LocalSymbol.lean#L404-L421

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

theorem GroundTheory.Global.InfinitePlace.natCard_kerModRange_normHom_cycSub (hv : v.IsReal) (hw : w.IsComplex) :
    Nat.card (KerModRange (normHom (unitsRep v w))
      (cycSub (unitsRep v w) (completionConj hv))) = 1 := by sorry
