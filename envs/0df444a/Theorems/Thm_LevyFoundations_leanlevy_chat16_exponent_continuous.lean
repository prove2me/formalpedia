-- Prove2me | Theorems.Thm_LevyFoundations_leanlevy_chat16_exponent_continuous
-- name    : LevyFoundations.leanlevy_chat16_exponent_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T13:00:38.273552+00:00
-- url     : https://prove2.me/theorems/f99f36c6-4668-43c8-8f6a-8c21f0783df7
-- title:
--   Continuity of every Levy-Khintchine exponent
-- statement:
--   The drift and Gaussian terms are continuous functions of frequency and the compensated Levy integral is continuous by locally dominated convergence.
-- source:
--   slink/LeanLevy commit 7e73fd9b23ad52956ec2756a815889a783131ce4, LeanLevy/Levy/LevyKhintchineProof.lean lines 5203-5208, exponent_continuous.

import Mathlib
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_levyKhintchineTriple
open MeasureTheory

theorem LevyFoundations.leanlevy_chat16_exponent_continuous
    (T : LevyFoundations.LevyKhintchineTriple) :
    Continuous (LevyFoundations.exponent T) := by sorry
