-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_theorem_2_3
-- name    : MultiSpinCounting.Positive.theorem_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:22:40.891256+00:00
-- url     : https://prove2.me/theorems/c5bb6464-fa06-464a-8928-26005183c5af
-- title:
--   Theorem 2.3 — exact linear-fractional optimization in the bit model
-- statement:
--   Let $L$ have rational affine numerator and denominator, free variables in $\mathbb R^d$, inequalities $Ax\le b$ with $m$ rows, a nonempty bounded feasible region, and a strictly positive denominator throughout that region. Its explicit Charnes–Cooper program has $d+1$ variables, $m+3$ inequalities and encoding length at most $C|L|$. The forward map and $x=y/t$ are inverse bijections on feasible points, with $t>0$ and preservation of objective values.
--
--   There are one absolute $C>0$ and fixed finite deterministic machines, chosen before all dimensions and programs, for the transformation and exact optimization. The optimizer returns an attained rational optimum, for either minimization or maximization, within
--   $$C\max\{1,d+m\}^4|L|^3$$
--   steps. For $d+m\ge1$ this is precisely the printed $C(d+m)^4|L|^3$ bound; the zero-dimensional case is retained with budget $C|L|^3$. Likewise $d+1\le C\max\{1,d\}$ and $m+3\le C\max\{1,m\}$ give the printed size bounds above threshold one and retain all smaller instances.
--
--   The statement includes an actual transformation machine and exact bit-model optimization, beyond the algebraic change of variables.
--
--   Differences from the source:
--   - encoding: binary rational data and bit operations → published binary serializers and a finite-stack FinTM2 machine, with time witnessed by TM2OutputsInTime; reason: the encoder only serializes input data; all stacks, control and program labels are finite, and a fixed macro cost is absorbed in the constant
--   - encoding: O(·) with an absolute implicit constant → one positive natural constant chosen before all inputs and dimensions; reason: the finitely many small encoding sizes are absorbed in this constant; no input is excluded
--   - encoding: O(d), O(m), and O((d+m)^4 |L|^3) → exact sizes d+1,m+3 and dimension thresholds one, with max 1 padding below threshold; reason: asymptotic notation has no literal zero budget at dimension zero; positive-dimensional exponents 4 and 3 are unchanged
--   - encoding: Charnes–Cooper equalities and free variables → two inequalities per equality on the reused unrestricted rational-LP data, with a direction bit; reason: both optimization directions and all feasible points and objective values are preserved
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), pp. 9–10, (2.3), Theorem 2.3 and its proof

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_LinearFractional

namespace MultiSpinCounting.Positive
open OnlineCRS.Combine

/-- Theorem 2.3, p. 10, all clauses. Threshold 1 for each dimension gives O(d), O(m);
zero dimensions are retained explicitly by max 1. No zero-step assertion at d=m=0. -/
theorem theorem_2_3 :
    ∃ (C : ℕ) (transform solve : BitMachine), 0 < C ∧
      ∀ (d m : ℕ) (L : AffineLFP d m),
        (lfpFeasible L).Nonempty → Bornology.IsBounded (lfpFeasible L) →
        (∀ x ∈ lfpFeasible L, 0 < denominator L x) →
        (encLP (charnesCooper L)).length ≤ C*(encLFP L).length ∧
        (d+1 ≤ C*max 1 d) ∧ (m+3 ≤ C*max 1 m) ∧
        (∀ x ∈ lfpFeasible L,
          ccForward L x ∈ lpFeasible (charnesCooper L) ∧
          ccInverse (ccForward L x) = x ∧
          lpValue (charnesCooper L) (ccForward L x) = lfpValue L x) ∧
        (∀ z ∈ lpFeasible (charnesCooper L),
          0 < z (0 : Fin (d+1)) ∧ ccInverse z ∈ lfpFeasible L ∧ ccForward L (ccInverse z) = z ∧
          lfpValue L (ccInverse z) = lpValue (charnesCooper L) z) ∧
        (∃ steps : ℕ, Runs transform (encLFP L) (encLP (charnesCooper L)) steps) ∧
        (∃ (r : ℚ) (steps : ℕ), IsLFPOptimum L r ∧
          Runs solve (encLFP L) (encRat r) steps ∧
          steps ≤ C*(max 1 (d+m))^4*(encLFP L).length^3) := by sorry

end MultiSpinCounting.Positive
