-- Prove2me | Theorems.Thm_MasulloRH_finite_prime_support_probability_escape
-- name    : MasulloRH.finite_prime_support_probability_escape
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:20:44.273097+00:00
-- url     : https://prove2.me/theorems/8053ad9d-dc66-423e-a7e0-a775c0b82050
-- title:
--   Finite prime support prevents a global probability law with Euler void probabilities
-- statement:
--   Let $X$ carry nonnegative summable weights $w_x$ of total mass one. Suppose each $x$ has a finite set $S_x$ of active primes, as holds for the valuations of any nonzero rational. Fix $0<a\le1$. There is a finite set $S$ such that, for all sufficiently large $B$, the probability that $S_x$ avoids every prime $p\le B$ outside $S$ is strictly larger than $\prod_{p\le B,\,p\notin S}(1-p^{-a})$. Thus the independent geometric prime-valuation laws cannot be the marginals of a single probability weight on rational shifts at these exponents. The theorem also applies if their proposed void probabilities are even smaller.
-- source:
--   Companion to finite prime orbit cutoffs https://prove2.me/theorems/fa50948f-56da-4d20-8046-d2063aeeba8d and their Euler scale https://prove2.me/theorems/cb9c879c-5f78-4ac2-9d8e-d6f142da2991. Uses divergence of reciprocal primes; compares the direct sum of rational valuation indices with finite product marginals.

import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
open Filter Finset
open scoped Topology

theorem MasulloRH.finite_prime_support_probability_escape {X : Type*} (supp : X → Finset ℕ) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : Summable w) (hm : ∑' x, w x = 1)
    (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ S : Finset ℕ, ∀ᶠ B : ℕ in atTop,
      let Q := (range (B+1)).filter (fun p => p.Prime ∧ p ∉ S)
      (∏ p ∈ Q, (1 - (p:ℝ)^(-a))) <
        ∑' x, (if Disjoint (supp x) Q then w x else 0) := by sorry
