-- Prove2me | Theorems.Thm_NemytskiiLebesgue_normSMulSelf_realLIE
-- name    : NemytskiiLebesgue.normSMulSelf_realLIE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T18:37:14.619698+00:00
-- url     : https://prove2.me/theorems/088d5750-1051-4084-897b-89724fab1e29
-- title:
--   Nemytskii Lebesgue: norm SMul Self real LIE
-- statement:
--   The Nemytskii Lebesgue construction uses the norm SMul Self real LIE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L40-L42
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/RealIso.lean#L40-L42

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Basic
public import Definitions.Def_LeanPool_NemytskiiLebesgue_RealIso
set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal

theorem NemytskiiLebesgue.normSMulSelf_realLIE {T : Type} (t : T) (s : ℝ) :
    normSMulSelf t (realLIE s) = realLIE (|s| * s) := by sorry
