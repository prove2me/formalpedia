-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_Supplement_formula_bounds_and_closure
-- name    : NCFactorClosure607.Circuits.Supplement.formula_bounds_and_closure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:11:37.091095+00:00
-- url     : https://prove2.me/theorems/2c0b0d29-660e-40d1-ba10-a499c71c80a3
-- title:
--   Theorem 1.2 — over any field, $\mathrm{VF}_{nc}$, $\mathrm{VP}_{nc}$ and $\mathrm{VNP}_{nc}$ are closed under factors; formula bounds $O(s^2)$ and $O(s^4)$
-- statement:
--   Let $F$ be any field. With families, polynomial bounds and the classes as in the Classes definition:
--
--   1. polynomial-size noncommutative formulas $\mathrm{VF}_{nc}$,
--   2. $\mathrm{VP}_{nc}$, and
--   3. $\mathrm{VNP}_{nc}$
--
--   are closed under taking factors: for all families with $f_n=a_ng_nb_n\neq0$ for every $n$, if $(f_n)$ belongs to the class then so does $(g_n)$, for every specified $(g_n)$.
--
--   4. More precisely, with one absolute constant $K$, for every set $X$ of noncommuting variables and every formula of size $s$ computing $f\neq0$:
--   $$f=gh\ \Rightarrow\ g,h\ \text{have formulas of size}\le Ks^2,\qquad f=agb\ \Rightarrow\ g\ \text{has a formula of size}\le Ks^4 .$$
--
--   This companion theorem extends the circuit closure of Theorem 1.1 to formulas, to the class $\mathrm{VP}_{nc}$, and to the Boolean-sum class $\mathrm{VNP}_{nc}$.
--
--   Differences from the source:
--   - generalization: X = {x_1, …, x_m} with m ≥ 1 → an arbitrary type X of noncommuting variables; reason: the statement for every type specializes to every finite nonempty variable set
--   - encoding: families with polynomially many variables; polynomially bounded quantities → m : ℕ → ℕ and f n ∈ F⟨x_1, …, x_{m n}⟩; u polynomially bounded iff u n ≤ c nᶜ + c for one c and all n; reason: standard nonuniform definitions [4]; the + c keeps n = 0 well defined
--   - generalization: polynomial-size formulas with the polynomial-variable family convention of §6 → formula families with polynomially bounded formula size and no bound on the ambient number of variables; reason: restricting to polynomially bounded m gives exactly the source class; the output family keeps that same m, and formula size already bounds degree
--   - encoding: degree of a VNP_nc verifier → ncDeg of the polynomial G_n ∈ F⟨X ∪ Z⟩; reason: §6.2 measures the degree of the verifier polynomial
--   - encoding: O(s²) and O(s⁴) → one absolute natural constant K quantified before the field, the variable type, the input and the factors; reason: the O(·) of the source is a uniform absolute constant
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.3, Theorem 1.2; proved on p.17 from Corollary 5.2 (p.12), §6.1 (p.14) and Theorem 6.1 (p.15); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Supplement_Classes

universe u v

namespace NCFactorClosure607.Circuits.Supplement

/-- Theorem 1.2 (Formula bounds and closure), p.3. Over any field `F`:
1. polynomial-size noncommutative formulas (`VF_nc`), 2. `VP_nc` and 3. `VNP_nc` are closed under
taking factors, i.e. for all families with `f_n = a_n g_n b_n ≠ 0` for every `n`, if `(f_n)` is
in the class then so is `(g_n)`;
4. quantitatively, with one absolute constant `K`: a one-sided factor (`g` or `h` in `f = g h`)
of a nonzero polynomial computed by a formula of size `s` has a formula of size at most `K s²`,
and a factor `g` in `f = a g b ≠ 0` has a formula of size at most `K s⁴`. -/
theorem formula_bounds_and_closure :
    (∀ (F : Type u) [Field F], ClosedUnderFactors F (VFnc F)) ∧
    (∀ (F : Type u) [Field F], ClosedUnderFactors F (VPnc F)) ∧
    (∀ (F : Type u) [Field F], ClosedUnderFactors F (VNPnc F)) ∧
    ∃ K : ℕ, ∀ (F : Type u) [Field F] (X : Type v) (Φ : Formula F X), Φ.eval ≠ 0 →
      (∀ g h : FreeAlgebra F X, Φ.eval = g * h →
        (∃ Ψ : Formula F X, Ψ.eval = g ∧ Ψ.size ≤ K * Φ.size ^ 2) ∧
        (∃ Ψ : Formula F X, Ψ.eval = h ∧ Ψ.size ≤ K * Φ.size ^ 2)) ∧
      (∀ a g b : FreeAlgebra F X, Φ.eval = a * g * b →
        ∃ Ψ : Formula F X, Ψ.eval = g ∧ Ψ.size ≤ K * Φ.size ^ 4) := by sorry

end NCFactorClosure607.Circuits.Supplement
