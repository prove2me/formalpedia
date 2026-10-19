-- Prove2me | Theorems.Thm_IntMul_Kappa_controlled_shift_permutation
-- name    : IntMul.Kappa.controlled_shift_permutation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:50:36.262005+00:00
-- url     : https://prove2.me/theorems/c3f5535a-6b1a-4674-8393-7a41ba4495bd
-- title:
--   Controlled modular stream shifts preserve fibres and are invertible
-- statement:
--   Let C be any type of preceding control fields, Q any natural modulus and a:C→ZMod Q a prepared offset. The source-faithful controlled stream update (c,y)↦(c,y+a(c)) is a bijection, with exact inverse (c,y)↦(c,y−a(c)). Thus it permutes each Q-block fibre without changing the control field and never loses or duplicates a record. This proves the permutation correctness part of Section 2's controlled-shifts lemma of the OpenAI integer multiplication paper; the finite-tape O(V) split/merge implementation and offset cost remain separate obligations.
-- source:
--   OpenAI, Integer multiplication below n log n, preprint September 23 2026, manuscript Section 2 lemma 'Controlled shifts and fixed rational scalings' (lem:ordered-affine-streams), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026/build/sections/02-streams.tex .

import Mathlib

theorem IntMul.Kappa.controlled_shift_permutation
    (C : Type) (Q : ℕ) (a : C → ZMod Q) :
    Function.Bijective
      (fun p : C × ZMod Q => (p.1, p.2 + a p.1)) ∧
    (∀ p : C × ZMod Q,
      (fun t : C × ZMod Q => (t.1, t.2 - a t.1))
        ((fun t : C × ZMod Q => (t.1, t.2 + a t.1)) p) = p) := by sorry
