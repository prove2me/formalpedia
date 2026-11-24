-- Prove2me | Theorems.Thm_GlobalTheory_SA_TransvG_det_updateRow_last
-- name    : GlobalTheory.SA.TransvG.det_updateRow_last
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:45:59.209794+00:00
-- url     : https://prove2.me/theorems/1b8a60f6-0c8b-402c-8ea1-0e95b860c0c8
-- title:
--   Transv G: det update Row last
-- statement:
--   The Transv G construction uses the det update Row last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetFromBlocksSingle.lean#L20-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DetFromBlocksSingle.lean#L20-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_SymmetricFlagBasisVectorsApplyCentre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DetFromBlocksSingle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.SA Matrix
open GlobalTheory GlobalTheory.SA GlobalTheory.SA.TransvG
variable {K : Type} [CommRing K]

theorem GlobalTheory.SA.TransvG.det_updateRow_last {r : ℕ} (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    (X.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).det = (X.submatrix Fin.castSucc Fin.castSucc).det := by sorry
