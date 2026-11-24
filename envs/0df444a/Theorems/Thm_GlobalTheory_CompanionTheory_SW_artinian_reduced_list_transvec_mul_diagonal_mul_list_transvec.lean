-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec
-- name    : GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:35.702855+00:00
-- url     : https://prove2.me/theorems/96346334-2f0c-439c-a06f-4b2d555fa63b
-- title:
--   SW: artinian reduced list transvec mul diagonal mul list transvec
-- statement:
--   The SW construction uses the artinian reduced list transvec mul diagonal mul list transvec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean#L114-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MatrixTransvectionDiagonalDecomposition.lean#L114-L125

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.artinian_reduced_list_transvec_mul_diagonal_mul_list_transvec
    (K : Type) [CommRing K] [IsArtinianRing K] [IsReduced K] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) :
    ∃ (L L' : List (Matrix.TransvectionStruct ι K)) (D : ι → K),
      A = (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D *
        (L'.map Matrix.TransvectionStruct.toMatrix).prod := by sorry
