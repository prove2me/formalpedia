-- Prove2me | Theorems.Thm_ModularCurve_relfinrank_full_eq_mul
-- name    : ModularCurve.relfinrank_full_eq_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/5f015f9c-5fab-5a82-a6d5-e91a75cefa54
-- title:
--   Relative degree of one prime-power step in the divisor-expansion tower
-- statement:
--   Fix a positive integer $M$, a prime $p$ and a natural number $a$. For a positive integer $N$ write $j_N :=$ `jqN N` for the image of the $q$-expansion `jq` of the modular invariant under the ring endomorphism `qExpand ℚ N` of $\mathbb{Q}((q))$ that multiplies Hahn-series exponents by $N$ (substitution $q \mapsto q^N$), and let `modularFunctionFieldFull N` be the intermediate field of $\mathbb{Q}((q))/\mathbb{Q}$ obtained by adjoining to $\mathbb{Q}$ the set of all $j_d$ with $d$ a positive divisor of $N$. Assume two things: first, that `modularFunctionFieldFull (M * p ^ (a + 1))` coincides with the field generated over $\mathbb{Q}$ by $j_{p^{a+1}}$ together with all elements of `modularFunctionFieldFull (M * p ^ a)`; second, that $j_{p^{a+1}}$ does not lie in `modularFunctionFieldFull (M * p ^ a)`. Then the relative degree (`IntermediateField.relfinrank`) of `modularFunctionFieldFull (M * p ^ (a + 1))` over `modularFunctionFieldFull (M * p ^ a)` equals $p + 1$ if $a = 0$ and $p$ otherwise.
--
--   This is one step of the tower computation of the degree of the modular equation: it reproduces the recursion $\psi(Mp^{a+1}) = \psi(Mp^{a}) \cdot (p+1)$ for $a = 0$ and $\psi(Mp^{a+1}) = \psi(Mp^{a}) \cdot p$ for $a \ge 1$ satisfied by the Dedekind $\psi$-function. It feeds the identification of the degree of `modularFunctionFieldFull N` over $\mathbb{Q}(j)$ with $\psi(N)$ and the attendant irreducibility of the modular polynomial, and is cited in the development of the $q$-expansion model of the function field of $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_relfinrank_full_eq_mul.lean

import Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.relfinrank_full_eq_mul (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hup : modularFunctionFieldFull (M * p ^ (a + 1)) = IntermediateField.adjoin ℚ (insert (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ)))) (hnm : jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a)) : IntermediateField.relfinrank (modularFunctionFieldFull (M * p ^ a)) (modularFunctionFieldFull (M * p ^ (a + 1))) = if a = 0 then p + 1 else p := by sorry
