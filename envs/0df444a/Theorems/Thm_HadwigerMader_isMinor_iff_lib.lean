-- Prove2me | Theorems.Thm_HadwigerMader_isMinor_iff_lib
-- name    : HadwigerMader.isMinor_iff_lib
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:51.147413+00:00
-- url     : https://prove2.me/theorems/a7cfd9e9-69bb-49ea-8b0f-bc78e0bb24f6
-- title:
--   Hadwiger Mader: is Minor iff lib
-- statement:
--   The minor notion of this file is that of `CliqueMinorsLib`.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L43-L51
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/Solution.lean#L43-L51

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_Minors
public import Definitions.Def_CliqueMinorsLib_MaderFive
public import Definitions.Def_HadwigerMader_Solution
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open HadwigerMader
variable {V W : Type*}

theorem HadwigerMader.isMinor_iff_lib {V W : Type*} (H : SimpleGraph W) (G : SimpleGraph V) :
    IsMinor H G ↔ CliqueMinors.IsMinor H G := by sorry
