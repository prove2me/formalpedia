-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArtinElem_mapMatrix_single
-- name    : GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:38.004834+00:00
-- url     : https://prove2.me/theorems/35caa0ed-1d8f-4279-a117-ddedc3731305
-- title:
--   Artin Elem: map Matrix single
-- statement:
--   The Artin Elem construction uses the map Matrix single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean#L23-L27

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

theorem GlobalTheory.CompanionTheory.SW.ArtinElem.mapMatrix_single (f : K →+* K') (a b : ι) (c : K) :
    f.mapMatrix (single a b c) = single a b (f c) := by sorry
