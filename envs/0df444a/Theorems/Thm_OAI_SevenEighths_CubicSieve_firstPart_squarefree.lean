-- Prove2me | Theorems.Thm_OAI_SevenEighths_CubicSieve_firstPart_squarefree
-- name    : OAI.SevenEighths.CubicSieve.firstPart_squarefree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:41:14.719243+00:00
-- url     : https://prove2.me/theorems/ad0f7163-f600-4d29-8ade-72074553bdeb
-- title:
--   Cubic Sieve: first Part squarefree
-- statement:
--   The Cubic Sieve construction uses the first Part squarefree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Factorization.lean#L49-L50
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/CubicSieve/Factorization.lean#L49-L50

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
omit [Subsingleton Mˣ]

theorem OAI.SevenEighths.CubicSieve.firstPart_squarefree (x : M) : Squarefree (firstPart x) := by sorry
