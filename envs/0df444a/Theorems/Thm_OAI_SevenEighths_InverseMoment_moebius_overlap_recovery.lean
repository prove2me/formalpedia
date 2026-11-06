-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_moebius_overlap_recovery
-- name    : OAI.SevenEighths.InverseMoment.moebius_overlap_recovery
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:54:15.232176+00:00
-- url     : https://prove2.me/theorems/7f5c8891-6c9b-4cf2-bca2-d8fc370e3662
-- title:
--   Inverse Moment: moebius overlap recovery
-- statement:
--   The Inverse Moment construction uses the moebius overlap recovery property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Overlap.lean#L21-L23
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Overlap.lean#L21-L23

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

theorem OAI.SevenEighths.InverseMoment.moebius_overlap_recovery {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by sorry
