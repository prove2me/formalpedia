-- Prove2me | Theorems.Thm_NCFactorClosure607_Circuits_circuit_implementation
-- name    : NCFactorClosure607.Circuits.circuit_implementation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:19:22.866748+00:00
-- url     : https://prove2.me/theorems/3ae6757a-2f7c-4688-b76f-b0ffa40763a6
-- title:
--   Lemma 4.1: $T(P)=c^{-1}[P((M_x)_x)]_{*,b}$ and a circuit for $T(P)$ of size $O(sb^3)$
-- statement:
--   Let cofactor data be given by a word $v$ of length $b\ge1$, a scalar $c\neq0$ and suffix coefficients $d_1,\dots,d_b$, with automaton map $T$ and transition matrices $M_x$.
--
--   1. Every polynomial $P\in F\langle X\rangle$ satisfies
--   $$T(P)=c^{-1}\bigl[P((M_x)_{x\in X})\bigr]_{*,b}. \tag{8}$$
--   2. There is an absolute constant $K$ such that, over every field and for every variable set, if $P$ is computed by a circuit $C$ of size $s$, then the matrix-substitution circuit $\mathrm{extractRight}(C,\text{data})$ computes $T(P)$, has size at most $K\,s\,b^3$, and has syntactic degree at most that of $C$.
--   3. For a scalar cofactor ($b=0$, $c\neq0$), the construction multiplies the output of $C$ by the constant $c^{-1}$: it computes $c^{-1}P$ with $s+2$ gates (one constant gate and one multiplication gate), and preserves the syntactic degree bound.
--
--   Together with Theorem 3.1 this yields a small circuit for $g$ from a circuit for $f=gh$.
--
--   Differences from the source:
--   - generalization: $X=\{x_1,\dots,x_m\}$ with $m\ge1$ → an arbitrary type `X`; reason: the statement for every type specializes to every finite nonempty variable set.
--   - generalization: data of a cofactor $h$ (a maximum-degree word of $h$, $c=[v]h$, the suffix coefficients of $h$) → arbitrary data with $|v|=b\ge1$ and $c\neq0$; reason: (8) and the construction use only $v$, $c$ and the $d_\ell$, and valid data of a cofactor are a special case.
--   - encoding: $O(sb^3)$ → one natural constant $K$ quantified before the field, the variable type, the circuit and the data; reason: the standard reading of an absolute $O$-constant.
--   - encoding: "Scalar cofactor removal uses one scalar multiplication" → the output is $c^{-1}P$ computed with one added constant gate $c^{-1}$ and one multiplication gate (size $s+2$); reason: in the gate-counting model a scalar multiplication is a constant input and a multiplication gate.
-- source:
--   V. Arvind, Pushkar S Joglekar, Factor Closure in Noncommutative Algebraic Complexity, STOC 2027 submission #607 (October 2026), p.9, Lemma 4.1, eq. (8), with eq. (7) and the scalar case of p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/607.pdf

import Mathlib
import Definitions.Def_NCFactorClosure607_Circuits_Extraction

universe u v

namespace NCFactorClosure607.Circuits

/-- Lemma 4.1 (p.9). (1) Identity (8): for data with `b ≥ 1` and `c ≠ 0`, every polynomial
satisfies `T(P) = c⁻¹ [P((M_x)_{x∈X})]_{∗,b}`. (2) There is one absolute constant `K` such that
for every field, every variable type, every well-formed circuit `C` and all such data, the
matrix-substitution circuit `extractRight C data` is a well-formed circuit computing
`T(C.eval)`, of size at most `K · size(C) · b³` and syntactic degree at most that of `C`.
(3) For a scalar cofactor (`b = 0`) the construction multiplies the output by the constant
`c⁻¹`, adding two gates (one constant, one multiplication). -/
theorem circuit_implementation :
    (∀ (F : Type u) [Field F] (X : Type v) (data : CofactorData F X),
        1 ≤ data.b → data.c ≠ 0 →
        ∀ P : FreeAlgebra F X,
          data.cofactorMap P =
            algebraMap F (FreeAlgebra F X) data.c⁻¹ *
              data.substMatrix P none (some (Fin.last data.b))) ∧
    (∃ K : ℕ, ∀ (F : Type u) [Field F] (X : Type v) (C : Circuit F X)
        (data : CofactorData F X),
        C.WellFormed → 1 ≤ data.b → data.c ≠ 0 →
          (extractRight C data).WellFormed ∧
          (extractRight C data).eval = data.cofactorMap C.eval ∧
          (extractRight C data).size ≤ K * C.size * data.b ^ 3 ∧
          (extractRight C data).synDeg ≤ C.synDeg) ∧
    (∀ (F : Type u) [Field F] (X : Type v) (C : Circuit F X) (data : CofactorData F X),
        C.WellFormed → data.b = 0 → data.c ≠ 0 →
          (extractRight C data).WellFormed ∧
          (extractRight C data).eval = algebraMap F (FreeAlgebra F X) data.c⁻¹ * C.eval ∧
          (extractRight C data).size = C.size + 2 ∧
          (extractRight C data).synDeg ≤ C.synDeg) := by sorry

end NCFactorClosure607.Circuits
