-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_mapMatrix_liftT_same
-- name    : GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_liftT_same
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:06.963958+00:00
-- url     : https://prove2.me/theorems/fde35c2b-a39a-478c-8c50-9355f26865ed
-- title:
--   Artin Elem: map Matrix lift T same
-- statement:
--   The Artin Elem construction uses the map Matrix lift T same property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean#L32-L35

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MatrixTransvectionDiagonalDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArtinElem
variable {K K' : Type*} [CommRing K] [CommRing K'] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [DecidableEq M] {F : M → Type*} [∀ m, CommRing (F m)]

theorem GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_liftT_same (e : K ≃+* ∀ m, F m) (m : M) (t : TransvectionStruct ι (F m)) :
    (coord e m).mapMatrix (liftT e m t).toMatrix = t.toMatrix := by sorry
