-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicSieve_extraction_injective_on_nonzero
-- name    : OAI.SevenEighths.CubicSieve.extraction_injective_on_nonzero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:41:21.551431+00:00
-- url     : https://prove2.me/theorems/0875fc82-08cd-4244-9ed0-13c226c882c5
-- title:
--   Cubic Sieve: extraction injective on nonzero
-- statement:
--   The Cubic Sieve construction uses the extraction injective on nonzero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Factorization.lean#L93-L100
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Factorization.lean#L93-L100

import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_Factorization
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

theorem OAI.SevenEighths.CubicSieve.extraction_injective_on_nonzero :
    Set.InjOn (fun x : M => (firstPart x, secondPart x, cubePart x)) {x | x ≠ 0} := by sorry
