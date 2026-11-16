-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_Supplement_computing_one_coefficient
-- name    : NCFactorClosure607.Circuits.Supplement.computing_one_coefficient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:13:01.456671+00:00
-- url     : https://prove2.me/theorems/6059212b-56f5-4e2d-b22d-9b9185f7a613
-- title:
--   Lemma 7.1 — one coefficient $[w]C$ in $O(\mathrm{size}(C)d^3)$ field operations, the empty-word coefficient in $O(\mathrm{size}(C))$
-- statement:
--   Let $F$ be a field, $X$ a set of variables, $C$ a circuit and $w$ a word of length $d$. There is an absolute constant $K$ such that the algorithm $\mathrm{coeffAlgo}$ returns the coefficient $[w]C$ of $w$ in the polynomial computed by $C$, and
--
--   1. if $d\ge1$, it performs at most $K\cdot\mathrm{size}(C)\cdot d^3$ field operations;
--   2. if $w=\varepsilon$, it performs at most $K\cdot\mathrm{size}(C)$ field operations.
--
--   $$[w]C\ \text{in}\ O(\mathrm{size}(C)\,d^3)\ \text{field operations}\quad(d\ge1),\qquad [\varepsilon]C\ \text{in}\ O(\mathrm{size}(C)).$$
--
--   No degree bound on intermediate gates is assumed. The lemma supplies the edge labels of Theorem 7.2 and the coefficient tests of the factorization algorithms.
--
--   Differences from the source:
--   - generalization: X = {x_1, …, x_m} with m ≥ 1 → an arbitrary type X with decidable equality; reason: decidable equality is needed to compare letters; every finite variable set has it
--   - encoding: the coefficient can be computed in O(size(C)d³) field operations → the explicit algorithm coeffAlgo stores every computed interval coefficient once and returns [w]C with at most K·size(C)·d³ counted field operations; reason: the operation count of the proof’s dynamic program, with later lookups reusing stored values
--   - encoding: O(size(C)d³) and O(size(C)) → one absolute natural constant K quantified before the field, the variable type, the input and the factors; reason: the O(·) of the source is a uniform absolute constant
--   - encoding: No degree bound on intermediate gates is needed → no syntactic-degree hypothesis on C; reason: the sentence states the absence of the hypothesis
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.17, Lemma 7.1 and its proof; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Supplement_CoeffAlgorithm

universe u v

namespace NCFactorClosure607.Circuits.Supplement

open NCFactorClosure607.Circuits

/-- Lemma 7.1 (Computing one coefficient), p.17. There is one absolute constant `K` such that for
every field `F`, every type `X` of variables, every well-formed circuit `C` (no degree bound on
any gate) and every word `w`, the algorithm `coeffAlgo` returns the coefficient `[w]C`, using at
most `K · size(C) · d³` field operations when `w` has length `d ≥ 1`, and at most `K · size(C)`
field operations for the empty word. -/
theorem computing_one_coefficient :
    ∃ K : ℕ, ∀ (F : Type u) [Field F] (X : Type v) [DecidableEq X] (C : Circuit F X)
      (w : List X), C.WellFormed →
      (coeffAlgo C w).1 = coeff (FreeMonoid.ofList w) C.eval ∧
      (1 ≤ w.length → (coeffAlgo C w).2 ≤ K * C.size * w.length ^ 3) ∧
      (w = [] → (coeffAlgo C w).2 ≤ K * C.size) := by sorry

end NCFactorClosure607.Circuits.Supplement
