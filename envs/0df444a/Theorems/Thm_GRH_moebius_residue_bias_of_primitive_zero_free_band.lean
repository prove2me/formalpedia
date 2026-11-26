-- Prove2me | Theorems.Thm_GRH_moebius_residue_bias_of_primitive_zero_free_band
-- name    : GRH.moebius_residue_bias_of_primitive_zero_free_band
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T13:04:27.952984+00:00
-- url     : https://prove2.me/theorems/fb1f3f07-3b94-4e4b-8433-c9677cb35114
-- title:
--   Möbius residue-class bias from zero exclusion for primitive characters at divisors of the modulus
-- statement:
--   Fix $q>0$, $1/2\le\alpha\le b=0.8749570698$ and $\sigma>\alpha$. Suppose each primitive nonprincipal character of positive conductor $d\mid q$ has no zero in $\alpha<\Re(s)\le b$. For each reduced residue class $a$ modulo $q$, its Möbius sum through $N$ differs from the average over all reduced classes by at most $C_a(N+1)^\sigma$ for all $N$.
-- source:
--   Derived in the centered Möbius bilinear problem https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and the square-cutoff residue-bias reduction https://prove2.me/theorems/ebfcf6de-c11b-4420-bb99-92e3875c1325.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Analysis.Complex.Polynomial.Basic

theorem GRH.moebius_residue_bias_of_primitive_zero_free_band (q : ℕ) [NeZero q] (α σ : ℝ)
    (hα : (1/2:ℝ) ≤ α) (hcap : α ≤ (0.8749570698:ℝ)) (hσ : α < σ)
    (hz : ∀ (d : ℕ) [NeZero d], d ∣ q → ∀ ψ : DirichletCharacter ℂ d,
      ψ.IsPrimitive → ψ ≠ 1 → ∀ s : ℂ,
      α < s.re → s.re ≤ (0.8749570698:ℝ) → ψ.LFunction s ≠ 0) :
    ∀ a : ZMod q, IsUnit a → ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |(∑ k ∈ Finset.range (N+1), if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) -
        (∑ k ∈ Finset.range (N+1), if IsUnit (k : ZMod q) then (ArithmeticFunction.moebius k : ℝ) else 0) /
          (q.totient : ℝ)| ≤ C * ((N : ℝ)+1)^σ := by sorry
