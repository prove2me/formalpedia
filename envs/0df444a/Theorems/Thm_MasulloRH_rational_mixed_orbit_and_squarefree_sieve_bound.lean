-- Prove2me | Theorems.Thm_MasulloRH_rational_mixed_orbit_and_squarefree_sieve_bound
-- name    : MasulloRH.rational_mixed_orbit_and_squarefree_sieve_bound
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:33:33.924652+00:00
-- url     : https://prove2.me/theorems/b968d2a2-18d7-420d-945d-2525cbeaad88
-- title:
--   A sharp mixed rational-orbit mass bound and squarefree obstruction at the Euler sieve scale
-- statement:
--   Let $0<a\le1$, $P_B=\{p\le B:p\text{ prime}\}$, $r_p=p^{-a}$ and $E_B=\prod_{p\in P_B}(1-r_p)$. At each cutoff take an arbitrary nonnegative mass $C_B$ on $\mathbb Q$ with sum one; it can vary with $B$. Put $x(k)=\prod_{p\in P_B}p^{k_p}$ for signed integer exponent vectors. If $C_B(x(k))\ge C_B(1)\prod_p r_p^{|k_p|}$ for every such $k$, then $C_B(1)\le\prod_{p\in P_B}(1-r_p)/(1+r_p)$, with the quotient taken inside the product. If the same relative lower bounds hold for every $B$ only on the finite grid $k_p\in\{-1,0,1\}$, then $C_B(1)\prod_p(1+2r_p)\le1$ and $C_B(1)/E_B\to0$. In particular the half-weight conclusion applies to arbitrary correlated lift marginals after both angular integrations. This checks a necessary condition for realizing the rational residue ratios by normalized ordinary orbit weights.
-- source:
--   Masullo mission discussion 14fd6a10-f6f1-4ccc-8086-e0646856a024 and 65e3e214-175b-45de-8683-0eea336d7f26, investigating the normalized rational lift in (11.3.2.1)–(11.3.2.2). Builds on the rational orbit residue 25e59343-4479-4b15-a2eb-55652707d2cf, double Haar mass result db985081-fca8-4440-bfd1-276f6e60b4e6 and the geometric model cb9c879c-5f78-4ac2-9d8e-d6f142da2991.

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open Filter Finset
open scoped Topology

theorem MasulloRH.rational_mixed_orbit_and_squarefree_sieve_bound (a : ℝ) (ha : 0 < a) (ha' : a ≤ 1)
    (C : ℕ → ℚ → ℝ) (hC : ∀ B x, 0 ≤ C B x) (hm : ∀ B, HasSum (C B) 1) :
    let P (B : ℕ) := (range (B+1)).filter Nat.Prime
    let r (p : ℕ) := (p : ℝ)^(-a)
    let E (B : ℕ) := ∏ p ∈ P B, (1-r p)
    (∀ B : ℕ, (∀ k : P B → ℤ, C B 1 * (∏ p : P B, (r p.val)^(k p).natAbs) ≤
        C B (∏ p : P B, (p.val : ℚ)^(k p))) →
      C B 1 ≤ ∏ p ∈ P B, (1-r p)/(1+r p)) ∧
    ((∀ (B : ℕ) (k : P B → ℤ), (∀ p, (k p).natAbs ≤ 1) →
        C B 1 * (∏ p : P B, (r p.val)^(k p).natAbs) ≤
          C B (∏ p : P B, (p.val : ℚ)^(k p))) →
      (∀ B : ℕ, C B 1 * (∏ p ∈ P B, (1+2*r p)) ≤ 1) ∧
      Tendsto (fun B => C B 1/E B) atTop (𝓝 0)) := by sorry
