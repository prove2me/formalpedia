-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_mapMatrix_liftT_ne
-- name    : GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_liftT_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:29.889546+00:00
-- url     : https://prove2.me/theorems/23ad32e9-56fc-4930-b6cc-3b73c5008f2c
-- title:
--   Artin Elem: map Matrix lift T ne
-- statement:
--   The Artin Elem construction uses the map Matrix lift T ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean#L37-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean#L37-L41

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

theorem GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_liftT_ne (e : K ≃+* ∀ m, F m) {m m' : M} (h : m' ≠ m)
    (t : TransvectionStruct ι (F m)) :
    (coord e m').mapMatrix (liftT e m t).toMatrix = 1 := by sorry
