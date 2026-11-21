-- Prove2me | Theorems.Thm_GRH_sharp_mobius_nonprincipal_above_record
-- name    : GRH.sharp_mobius_nonprincipal_above_record
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:32:31.001188+00:00
-- url     : https://prove2.me/theorems/3bef2215-4b82-447c-9616-29692b3651c6
-- title:
--   Power saving for finite nonprincipal character twists of Möbius above the zero-free exponent
-- statement:
--   Let $q$ be a positive integer, let $\chi$ be a nonprincipal Dirichlet character modulo $q$, and let $\mu$ be the Möbius function. For each real $\sigma>0.8749570698$,
--   $$
--   \sum_{1\le n\le N} \mu(n)\chi(n)=O_{\chi,\sigma}(N^\sigma)\qquad(N\to\infty).
--   $$
--   The sum has a sharp cutoff at $N$. This gives a power saving for every $0.8749570698<\sigma<1$ and includes imprimitive nonprincipal characters.
-- source:
--   An arithmetic application of the fixed zero-free region for Dirichlet L-functions (https://prove2.me/theorems/3a8f3264-d5ab-422c-8e4f-a2c0e27d6918), the associated subpower reciprocal estimate (https://prove2.me/theorems/002e2873-7fe9-49e9-aa82-096600ec5d26), and Titchmarsh’s holomorphic Perron bound (https://prove2.me/theorems/0cfc5f9d-8e47-4920-b235-f80b5f4f55a7).

import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs

open Filter Asymptotics

theorem GRH.sharp_mobius_nonprincipal_above_record (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (σ : ℝ)
    (hσ : (0.8749570698 : ℝ) < σ) :
    (fun n : ℕ => ∑ k ∈ Finset.range (n+1), χ k * (ArithmeticFunction.moebius k : ℂ))
      =O[atTop] (fun n : ℕ => (n : ℝ) ^ σ) := by sorry
