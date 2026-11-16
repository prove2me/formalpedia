-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_Supplement_common_bound_for_all_factors
-- name    : NCFactorClosure607.Circuits.Supplement.common_bound_for_all_factors
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:14:02.301356+00:00
-- url     : https://prove2.me/theorems/5c34affd-5ff2-4f6d-863d-34a8594b4123
-- title:
--   Remark 4.2 — every factor of a circuit of syntactic degree $\le D$ has a circuit of size $\le KsD^6$ and syntactic degree $\le D$
-- statement:
--   Let $F$ be a field and $X$ a set of noncommuting variables. There is an absolute constant $K\ge1$ such that for every circuit of size $s$ and syntactic degree at most $D$, where $D\ge1$, every factor $g$ of the polynomial it computes ($f=agb$ with $a,g,b\neq0$) has a circuit of size at most
--   $$B(s,D)=KsD^6$$
--   and syntactic degree at most $D$.
--
--   The bound is in terms of the original circuit; it does not grow when a factor is split further, which is what the bounded search of Theorems 8.1 and 8.2 relies on.
--
--   Differences from the source:
--   - generalization: X = {x_1, …, x_m} with m ≥ 1 → an arbitrary type X of noncommuting variables; reason: the statement for every type specializes to every finite nonempty variable set
--   - reading: fix an absolute constant K ≥ 1 large enough that B(s, D) = KsD⁶ bounds the above construction. Every factor has a circuit of size at most B(s, D) → ∃ K ≥ 1 such that every factor has a well-formed circuit of size ≤ K·s·D⁶ and syntactic degree ≤ D; reason: the Remark's conclusion; the last sentence is explanatory
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.10, Remark 4.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Circuit
import Definitions.Def_NCFactorClosure607_Circuits_Polynomials

universe u v

namespace NCFactorClosure607.Circuits.Supplement

open NCFactorClosure607.Circuits

/-- Remark 4.2 (A common bound for all factors), p.10. There is one absolute constant `K ≥ 1`
such that for every field `F`, every type `X` of noncommuting variables, every well-formed
circuit `C` of size `s` and syntactic degree at most `D ≥ 1`, and every factor `g` of its output
(`C.eval = a g b` with `a, g, b ≠ 0`), `g` has a circuit of size at most `B(s, D) = K s D⁶` and
syntactic degree at most `D`. -/
theorem common_bound_for_all_factors :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ (F : Type u) [Field F] (X : Type v) (C : Circuit F X) (D : ℕ),
      C.WellFormed → 1 ≤ D → C.synDeg ≤ D →
      ∀ a g b : FreeAlgebra F X, C.eval = a * g * b → a ≠ 0 → g ≠ 0 → b ≠ 0 →
        ∃ C' : Circuit F X, C'.WellFormed ∧ C'.eval = g ∧ C'.size ≤ K * C.size * D ^ 6 ∧
          C'.synDeg ≤ D := by sorry

end NCFactorClosure607.Circuits.Supplement
