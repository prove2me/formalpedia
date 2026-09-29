-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_abs_pointHt_sub_add_pointHt_le
-- name    : ModularCurve.JZero.exists_abs_pointHt_sub_add_pointHt_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/5cbbf8d2-49ba-556f-b6b3-5e422221282a
-- title:
--   Additivity up to O(1) of model heights on X₀(N)
-- statement:
--   Fix $N \geq 1$ with $N \neq 0$ as a type-class hypothesis, and let $F = \overline{F}_N$ denote [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), the subfield of the Laurent series field over $\overline{\mathbb{Q}}$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the modular function field $\mathbb{Q}(\text{divisorExpansions } N)$. Let $a,b,c$ be natural numbers and let $sA : \mathrm{Fin}\,a \to F$, $sB : \mathrm{Fin}\,b \to F$, $w : \mathrm{Fin}\,c \to F$ be finite families of elements of $F$, all of whose members are assumed nonzero. Let $A, B$ be divisors of $F/\overline{\mathbb{Q}}$, that is, finitely supported $\mathbb{Z}$-valued functions on the set of places [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22) of $F$ over $\overline{\mathbb{Q}}$, and assume that $\deg A$ and $\deg B$ (each place weighted by its residue degree) are at least $2g+1$, where $g$ is [`AlgebraicCurve.genusFF`](def/AlgebraicCurve_Repartitions.html#L145), the $\overline{\mathbb{Q}}$-dimension of $H^1$ of the zero divisor. Assume further that the $\overline{\mathbb{Q}}$-spans of the ranges of $sA$, $sB$ and $w$ are exactly the Riemann–Roch spaces $L(A) = \{f : v(f) \leq \exp(A(v)) \text{ for all } v\}$, $L(B)$ and $L(A+B)$ respectively. The conclusion is that there is a real constant $C$ such that for every place $v$ of $F$ over $\overline{\mathbb{Q}}$, $$\bigl| \mathrm{pointHt}(w, v) - \bigl( \mathrm{pointHt}(sA, v) + \mathrm{pointHt}(sB, v) \bigr) \bigr| \leq C,$$ where $\mathrm{pointHt}(s, v)$ is the absolute logarithmic height `absLogHeight` of the vector obtained by evaluating the $s_i$ at $v$ after normalising by a pivot coordinate.
--
--   This is the additivity $h_{A+B} = h_A + h_B + O(1)$ of the Weil height machine, expressed for the model heights attached to complete linear systems on the modular curve $X_0(N)$ over $\overline{\mathbb{Q}}$. It feeds the comparison of such model heights with the height of a regular value and, through that, the bound on the self-pairing of a chord used in the height-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_abs_pointHt_sub_add_pointHt_le.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JZero.exists_abs_pointHt_sub_add_pointHt_le (N : ℕ) [NeZero N]
    {a b c : ℕ} (sA : Fin a → ↥(ModularCurve.modularFunctionFieldBar N)) (sB : Fin b → ↥(ModularCurve.modularFunctionFieldBar N))
    (w : Fin c → ↥(ModularCurve.modularFunctionFieldBar N))
    (hA0 : ∀ i, sA i ≠ 0) (hB0 : ∀ j, sB j ≠ 0) (hw0 : ∀ l, w l ≠ 0)
    (A B : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hA : 2 * (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) + 1 ≤ A.degree)
    (hB : 2 * (AlgebraicCurve.genusFF (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℤ) + 1 ≤ B.degree)
    (hsA : Submodule.span (AlgebraicClosure ℚ) (Set.range sA) = AlgebraicCurve.riemannRochSpace A)
    (hsB : Submodule.span (AlgebraicClosure ℚ) (Set.range sB) = AlgebraicCurve.riemannRochSpace B)
    (hw : Submodule.span (AlgebraicClosure ℚ) (Set.range w) = AlgebraicCurve.riemannRochSpace (A + B)) :
    ∃ C : ℝ, ∀ v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N),
      |AlgebraicCurve.pointHt w v - (AlgebraicCurve.pointHt sA v + AlgebraicCurve.pointHt sB v)| ≤ C := by sorry
