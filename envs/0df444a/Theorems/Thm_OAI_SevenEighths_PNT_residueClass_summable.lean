-- Prove2me | Theorems.Thm_OAI_SevenEighths_PNT_residueClass_summable
-- name    : OAI.SevenEighths.PNT.residueClass_summable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:23:22.769766+00:00
-- url     : https://prove2.me/theorems/750cc713-3ed2-46c4-ad87-b6ae37537320
-- title:
--   PNT: residue Class summable
-- statement:
--   The PNT construction uses the residue Class summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeCounting/Progressions.lean#L22-L28
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/PrimeCounting/Progressions.lean#L22-L28

import Definitions.Def_PrimeNumberTheoremAnd_Wiener
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeCounting_Progressions
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.PNT
open Filter ArithmeticFunction LSeries
open scoped Topology

theorem OAI.SevenEighths.PNT.residueClass_summable {q : ℕ} (a : ZMod q) {σ : ℝ} (hσ : 1 < σ) :
    Summable (nterm (fun n => (vonMangoldt.residueClass a n : ℂ)) σ) := by sorry
