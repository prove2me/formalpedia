-- Prove2me | Theorems.Thm_N25_fifth_root_exp_ne_rat
-- name    : N25.fifth_root_exp_ne_rat
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:48.156875+00:00
-- url     : https://prove2.me/theorems/eaa65e8b-e447-4c22-a5a6-ec4e44386b64
-- title:
--   A nontrivial fifth root of unity is not rational
-- statement:
--   Let $v\in\mathbb Z$ be not divisible by $5$ and let $c\in\mathbb Q$. Then the nontrivial fifth root of unity determined by $v$ is not equal to $c$:
--
--   $$e^{-2\pi i v/5}\ne c.$$
--
--   This excludes rational residues in the width-$5$ cusp calculation.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib

set_option autoImplicit false

theorem N25.fifth_root_exp_ne_rat (v : ℤ) (hv : ¬ (5 : ℤ) ∣ v) (c : ℚ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((v : ℂ) / 5))) ≠ (c : ℂ) := by sorry
