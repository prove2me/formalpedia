-- Prove2me | Theorems.Thm_GRH_sharp_mobius_character_power_bound
-- name    : GRH.sharp_mobius_character_power_bound
-- status  : Open
-- author  : @Yi
-- created : 2026-11-21T00:03:03.620162+00:00
-- url     : https://prove2.me/theorems/49dd669e-eef2-4490-bed4-eb3e17c31635
-- title:
--   Square-root cancellation up to an epsilon in finite Dirichlet-character twists of Möbius
-- statement:
--   For each fixed positive modulus $q$, Dirichlet character $\chi$ modulo $q$, and exponent $1/2<\sigma<1$, the finite sums satisfy $\big|\sum_{1\le k\le N}\mu(k)\chi(k)\big|=O_{q,\chi,\sigma}(N^\sigma)$. The $k=0$ term in Lean vanishes. This is an open square-root cancellation estimate for the twisted Mertens function.
-- source:
--   Proposed finite-sum version of GRH.smoothed_mobius_character_power_bound, connected by Abel summation. The corresponding smoothed Mellin criterion and definition are in https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L81-L169

import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Defs

open Filter Asymptotics

theorem GRH.sharp_mobius_character_power_bound
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    (fun n : ℕ => ∑ k ∈ Finset.range (n+1),
      χ k * (ArithmeticFunction.moebius k : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ σ) := by sorry
