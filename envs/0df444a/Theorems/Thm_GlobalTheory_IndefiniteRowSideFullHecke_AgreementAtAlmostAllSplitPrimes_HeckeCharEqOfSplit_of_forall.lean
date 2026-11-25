-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_AgreementAtAlmostAllSplitPrimes_HeckeCharEqOfSplit_of_forall
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.HeckeCharEqOfSplit.of_forall
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:36.099868+00:00
-- url     : https://prove2.me/theorems/afb7e2d0-7066-4ce1-a7f3-977bc696a1ba
-- title:
--   Hecke Char Eq Of Split: of forall
-- statement:
--   The Hecke Char Eq Of Split construction uses the of forall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/AgreementAtAlmostAllSplitPrimes.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ThetaLiftGeometry/AgreementAtAlmostAllSplitPrimes.lean#L27-L30

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ThetaLiftGeometry_AgreementAtAlmostAllSplitPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes

theorem GlobalTheory.IndefiniteRowSideFullHecke.AgreementAtAlmostAllSplitPrimes.HeckeCharEqOfSplit.of_forall {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}
    {A : NAut N} (h : HeckeCharEqOfSplit N A) (χ χ' : A.CG 1)
    (hw : ∀ w, IsSplitPl H w → A.locG χ w = A.locG χ' w) : χ = χ' := by sorry
