-- Prove2me | Theorems.Thm_GRH_moebius_partial_sum_reduced_progression_power_bound
-- name    : GRH.moebius_partial_sum_reduced_progression_power_bound
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T00:13:56.008016+00:00
-- url     : https://prove2.me/theorems/c2e8263f-75e5-4e6c-a57c-32bc7d41e73b
-- title:
--   Möbius cancellation up to a sharp cutoff in each reduced residue class
-- statement:
--   Fix a positive modulus $q$, a unit residue class $a\bmod q$, and a real number $1/2<\sigma<1$. There is a constant $C=C(q,a,\sigma)\geq 0$ such that, for every integer $N\geq0$,
--   $$
--   \left|\sum_{\substack{1\leq n\leq N\\ n\equiv a\pmod q}}\mu(n)\right|\leq C(N+1)^\sigma.
--   $$
--
--   This is an open cancellation estimate for finite, real-valued sums. The modulus is fixed and the constant may depend on the residue class. For $q=1$ the sum is the ordinary Mertens function. Ye's Theorem 1.1 gives a stronger bound under GRH. The present problem asks for the stated fixed-modulus estimate unconditionally.
-- source:
--   Open unconditional fixed-modulus conjecture. For the GRH-conditional bound and the definition of M(x;q,a), see Lynnelle Ye, Bounding sums of the Möbius function over arithmetic progressions, arXiv:1406.7326, Theorem 1.1 (p. 4) and §2 (p. 5), https://arxiv.org/pdf/1406.7326 .

import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators

theorem GRH.moebius_partial_sum_reduced_progression_power_bound
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ Finset.range (n + 1),
        if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0| ≤
          C * ((n : ℝ) + 1) ^ σ := by sorry
