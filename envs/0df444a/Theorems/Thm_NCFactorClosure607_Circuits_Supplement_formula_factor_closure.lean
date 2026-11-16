-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_Supplement_formula_factor_closure
-- name    : NCFactorClosure607.Circuits.Supplement.formula_factor_closure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:11:00.435466+00:00
-- url     : https://prove2.me/theorems/06acaf95-adc9-4f60-acba-182378c3aa9a
-- title:
--   Corollary 5.2 — one-sided factors of a size-$s$ formula have formulas of size $O(s^2)$, central factors $O(s^4)$
-- statement:
--   Let $F$ be a field and $X$ a set of noncommuting variables. There is an absolute constant $K$ such that, whenever a formula of size $s$ computes a nonzero polynomial $f\in F\langle X\rangle$:
--
--   1. if $f=gh$, then both $g$ and $h$ have formulas of size at most $Ks^2$;
--   2. if $f=agb$, then $g$ has a formula of size at most $Ks^4$.
--
--   $$f=gh\neq0\ \Rightarrow\ L(g),L(h)\le Ks^2,\qquad f=agb\neq0\ \Rightarrow\ L(g)\le Ks^4,$$
--   where $L(\cdot)$ is the least formula size. This is the quantitative formula clause of Theorem 1.2.
--
--   Differences from the source:
--   - generalization: X = {x_1, …, x_m} with m ≥ 1 → an arbitrary type X of noncommuting variables; reason: the statement for every type specializes to every finite nonempty variable set
--   - encoding: O(s²) and O(s⁴) → one absolute natural constant K quantified before the field, the variable type, the input and the factors; reason: the O(·) of the source is a uniform absolute constant
--   - encoding: each one-sided factor → both g and h in every presentation f = g h; reason: a left factor is g in f = gh and a right factor is h in f = gh (p.5)
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.12, Corollary 5.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Supplement_Formula

universe u v

namespace NCFactorClosure607.Circuits.Supplement

/-- Corollary 5.2 (Formula factor closure), p.12. There is one absolute constant `K` such that
for every field `F`, every type `X` of noncommuting variables and every formula `Φ` of size `s`
computing a nonzero `f`: if `f = g h` then `g` and `h` have formulas of size at most `K s²`, and
if `f = a g b` then `g` has a formula of size at most `K s⁴`. -/
theorem formula_factor_closure :
    ∃ K : ℕ, ∀ (F : Type u) [Field F] (X : Type v) (Φ : Formula F X), Φ.eval ≠ 0 →
      (∀ g h : FreeAlgebra F X, Φ.eval = g * h →
        (∃ Ψ : Formula F X, Ψ.eval = g ∧ Ψ.size ≤ K * Φ.size ^ 2) ∧
        (∃ Ψ : Formula F X, Ψ.eval = h ∧ Ψ.size ≤ K * Φ.size ^ 2)) ∧
      (∀ a g b : FreeAlgebra F X, Φ.eval = a * g * b →
        ∃ Ψ : Formula F X, Ψ.eval = g ∧ Ψ.size ≤ K * Φ.size ^ 4) := by sorry

end NCFactorClosure607.Circuits.Supplement
