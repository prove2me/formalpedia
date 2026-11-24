-- Prove2me | Theorems.Thm_GlobalTheory_LineThrough_isMaximal_of_ker_lineMap_lt
-- name    : GlobalTheory.LineThrough.isMaximal_of_ker_lineMap_lt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:11:40.471916+00:00
-- url     : https://prove2.me/theorems/58fd58c6-6076-450c-b203-6df3265eafbb
-- title:
--   Line Through: is Maximal of ker line Map lt
-- statement:
--   The Line Through construction uses the is Maximal of ker line Map lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L65-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsPrimeDimensionLEOneAvoiding.lean#L65-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough

theorem GlobalTheory.LineThrough.isMaximal_of_ker_lineMap_lt {d : ℕ} (a c : Fin d → ℂ)
    (P : Ideal (MvPolynomial (Fin d) ℂ)) [hP : P.IsPrime] (h : RingHom.ker (lineMap a c) < P) :
    P.IsMaximal := by sorry
