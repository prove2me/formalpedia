-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_Supplement_applying_map_to_formula
-- name    : NCFactorClosure607.Circuits.Supplement.applying_map_to_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:10:22.219007+00:00
-- url     : https://prove2.me/theorems/445a7316-116d-4583-aa53-8a08677c1e10
-- title:
--   Lemma 5.1 — applying the cofactor-removal map to a formula: size $O(s^2)$, $O(sb^3)$ field operations, $O(s^2)$ writing operations
-- statement:
--   Let $F$ be a field, $X$ a set of noncommuting variables, and fix cofactor data (a word $v$ of length $b$, a scalar $c\neq0$, suffix coefficients $d_\ell$) with automaton map $T$. Let $\Phi$ be a formula of size $s$ computing $P$. There is an absolute constant $K$ such that the direct construction $\mathrm{formulaExtract}(\Phi,\text{data})$ of §5.1 satisfies the following.
--
--   It outputs a formula for $T(P)$ of size at most $Ks^2$ for every $b$, including $b=0$.
--
--   1. If $b\ge1$, it performs at most $Ksb^3$ field operations and at most $Ks^2$ operations to write the formula.
--   2. If $b=0$ (a scalar cofactor), it outputs the scalar multiple $c^{-1}\cdot\Phi$ of the original formula, which computes $T(P)$, with one field operation.
--
--   $$|\text{formula for }T(P)|=O(s^2),\qquad \#\text{field operations}=O(sb^3),\qquad \#\text{writing operations}=O(s^2).$$
--
--   This is the formula analogue of the circuit implementation of Lemma 4.1, and the step from which Corollary 5.2 and the formula clauses of Theorem 1.2 follow.
--
--   Differences from the source:
--   - generalization: X = {x_1, …, x_m} with m ≥ 1 → an arbitrary type X of noncommuting variables; reason: the statement for every type specializes to every finite nonempty variable set
--   - generalization: NFA data of a cofactor h (a longest word of h, its coefficient c and the coefficients of its suffixes) → any cofactor data with c ≠ 0; reason: for b ≥ 1 the construction computes c⁻¹[P(M)]_{∗,b} = T(P) by eq. (8) of Lemma 4.1, without cofactor validity; for b = 0 both the construction and T directly scale P by c⁻¹; valid data are a special case
--   - encoding: O(s²) formula size, O(sb³) field operations and O(s²) writing operations → one absolute natural constant K quantified before the field, the variable type, the input and the factors; reason: the O(·) of the source is a uniform absolute constant
--   - encoding: the formula can be constructed using O(sb³) field operations and O(s²) operations to write the formula → the counts recorded by formulaExtract with scalar matrices, columns and reset coefficients stored as finite lists of computed entries; one operation per field addition, multiplication, negation or inversion, and one per formula node written; reason: the proof computes and stores each scalar entry once; later lookups incur no field arithmetic
--   - reading: a scalar cofactor requires only scalar multiplication of the original formula → for b = 0 the output is exactly c⁻¹ · Φ, it computes T(P), and one field operation (the inversion of c) is performed; reason: the literal content of the sentence
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.10, Lemma 5.1; proof pp.10–12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Supplement_FormulaExtraction

universe u v

namespace NCFactorClosure607.Circuits.Supplement

open NCFactorClosure607.Circuits

/-- Lemma 5.1 (Applying the map to a formula), p.10. There is one absolute constant `K` such
that for every field `F`, every type `X` of noncommuting variables, every formula `Φ` of size `s`
computing `P`, and all cofactor data with `c ≠ 0`, the explicit construction `formulaExtract`
(proof of Lemma 5.1, p.10–12):
* outputs a formula for `T(P)` of size at most `K s²`, including scalar cofactors;
* for `b ≥ 1` performs at most `K s b³` field operations and at most `K s²`
  formula-writing operations;
* for a scalar cofactor (`b = 0`) outputs the scalar multiple `c⁻¹ · Φ` of the original formula,
  a formula for `T(P)`, with one field operation. -/
theorem applying_map_to_formula :
    ∃ K : ℕ, ∀ (F : Type u) [Field F] (X : Type v) (Φ : Formula F X)
      (data : CofactorData F X), data.c ≠ 0 →
      (formulaExtract Φ data).formula.eval = data.cofactorMap Φ.eval ∧
      (formulaExtract Φ data).formula.size ≤ K * Φ.size ^ 2 ∧
      (1 ≤ data.b →
        (formulaExtract Φ data).fieldOps ≤ K * Φ.size * data.b ^ 3 ∧
        (formulaExtract Φ data).writeOps ≤ K * Φ.size ^ 2) ∧
      (data.b = 0 →
        (formulaExtract Φ data).formula = .mul (.const data.c⁻¹) Φ ∧
        (formulaExtract Φ data).fieldOps = 1) := by sorry

end NCFactorClosure607.Circuits.Supplement
