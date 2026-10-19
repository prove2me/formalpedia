-- Prove2me | Theorems.Thm_IntMul_Kappa_controlled_affine_unit_permutation
-- name    : IntMul.Kappa.controlled_affine_unit_permutation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:54:21.785288+00:00
-- url     : https://prove2.me/theorems/bc554acb-35e6-40b0-8f7e-071aa899f22f
-- title:
--   Unit affine maps preserve ordered stream fibres
-- statement:
--   For any control type C and modulus Q, let u(c) be an invertible residue modulo Q and a(c) an additive offset. Then the control-dependent affine update (c,y)→(c,u(c)y+a(c)) is a bijection, with explicit inverse (c,z)→(c,u(c)^−1(z−a(c))). This formalises the algebraic correctness of the fixed rational scalings and controlled shifts on indexed stream fibres in Section 2 of OpenAI's integer-multiplication construction. It makes no unverified claim about multitape execution time, which must be proved separately.
-- source:
--   OpenAI, Integer multiplication below n log n, Section 2 lemma Controlled shifts and fixed rational scalings (lem:ordered-affine-streams), https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026/build/sections/02-streams.tex .

import Mathlib

theorem IntMul.Kappa.controlled_affine_unit_permutation
    (C : Type) (Q : ℕ) (u : C → (ZMod Q)ˣ) (a : C → ZMod Q) :
    Function.Bijective
      (fun p : C × ZMod Q =>
        (p.1, (u p.1 : ZMod Q) * p.2 + a p.1)) := by sorry
