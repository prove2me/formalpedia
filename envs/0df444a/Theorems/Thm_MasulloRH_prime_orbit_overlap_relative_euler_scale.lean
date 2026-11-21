-- Prove2me | Theorems.Thm_MasulloRH_prime_orbit_overlap_relative_euler_scale
-- name    : MasulloRH.prime_orbit_overlap_relative_euler_scale
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:18:09.94767+00:00
-- url     : https://prove2.me/theorems/cb9c879c-5f78-4ac2-9d8e-d6f142da2991
-- title:
--   The prime orbit zero-shift overlap decays strictly faster than the scalar Euler sieve factor
-- statement:
--   Fix $0<a\le1$. For primes $p\le B$ write $r_p=p^{-a}$, $E_B=\prod_{p\le B}(1-r_p)$ and $C_B=\prod_{p\le B}\frac{1-r_p}{1+r_p}$, with each ratio inside the product. The latter is the limiting zero-shift overlap of the normalized geometric box cutoff at fixed $B$. Then $E_B>0$ and $$\frac{C_B}{E_B}=\left(\prod_{p\le B}(1+r_p)\right)^{-1}\longrightarrow 0.$$ This compares the absolute geometric orbit mass with the finite scalar sieve normalization in the rational trace model.
-- source:
--   Companion to the accepted normalized orbit cutoff https://prove2.me/theorems/fa50948f-56da-4d20-8046-d2063aeeba8d and finite scalar sieve theorem https://prove2.me/theorems/c2c832e0-37f7-48a3-9a12-809625c31683. Uses Euler’s divergence of reciprocal primes.

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Filter Finset
open scoped Topology

theorem MasulloRH.prime_orbit_overlap_relative_euler_scale (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1) :
    let P (B : ℕ) := (range (B+1)).filter Nat.Prime
    let r (p : ℕ) := (p : ℝ)^(-a)
    let C (B : ℕ) := ∏ p ∈ P B, (1-r p)/(1+r p)
    let E (B : ℕ) := ∏ p ∈ P B, (1-r p)
    (∀ B, 0 < E B ∧ C B / E B = (∏ p ∈ P B, (1+r p))⁻¹) ∧
    Tendsto (fun B => C B / E B) atTop (𝓝 0) := by sorry
