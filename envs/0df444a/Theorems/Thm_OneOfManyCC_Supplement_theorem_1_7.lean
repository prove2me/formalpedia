-- Prove2me | Theorems.Thm_OneOfManyCC_Supplement_theorem_1_7
-- name    : OneOfManyCC.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:23:22.862918+00:00
-- url     : https://prove2.me/theorems/c0438adb-82c7-49fa-b160-14f9f2ad7c45
-- title:
--   Theorem 1.7 — every nonconstant $g$ has a core $S^m$ on which $\mathrm{CC}(R_g(X))\ge D(g)-O(\log n)$ at relative density $(1+2^{1-m})/3$
-- statement:
--   Let $g:\{0,1\}^n\to\{0,1\}$ be a nonconstant total function and $D(g)$ its De Morgan formula depth. For $X\subseteq(\{0,1\}^n)^m$, let $R_g(X)$ be the restriction of $U_m\diamond\mathrm{KW}_g$ to $X\times X$: on $A,B\in X$ the players output a cell $(i,j)$ with $A_{i,j}\ne B_{i,j}$, or reject when $g^m(A)=g^m(B)$.
--
--   There is an absolute constant $C>0$ such that for every $n$ and every such $g$ there is a nonempty $S\subseteq\{0,1\}^n$ with the following property: for every $m\ge2$ and every $X\subseteq S^m$ with
--   $$|X|\ge\frac{1+2^{1-m}}{3}\,|S|^m,$$
--   we have
--   $$\mathrm{CC}(R_g(X))\ge D(g)-C\log_2 n.$$
--
--   The single set $S$ works for all $m\ge2$; the density threshold is $1/2$ at $m=2$ and tends to $1/3$. This answers the hard-core question of Dinur and Meir for every nonconstant function with an $O(\log n)$ loss.
--
--   **Formalization Note** $S^m$ is the set of matrices all of whose rows lie in $S$; the relative density of $X$ in it is $|X|/|S|^m$, compared in $\mathbb R$. $D(g)$ is `D (fun x => some (g x))`.
--
--   Differences from the source:
--   - encoding: O(log n) → one absolute constant C > 0 chosen before every type and parameter, with base-2 logarithms (Real.logb 2); reason: the paper's O(·) hides an absolute constant; logarithms are base 2 (§3)
--   - encoding: nonconstant g; core Sᵐ; relative density |X|/|Sᵐ| ≥ (1 + 2¹⁻ᵐ)/3 → ∃ x y, g x ≠ g y; X ⊆ {Z | ∀ i, Z i ∈ S}; ((1 + 2^(1−m))/3)·|S|^m ≤ |X| in ℝ; reason: the same sets and the same density condition, |Sᵐ| = |S|ᵐ
--   - encoding: D(g) for total g; R_g(X) on X × X → D (fun x => some (g x)); Rg g X on the subtype ↥X; reason: a total function is a partial function with no ∗; the density bound makes X nonempty
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.7, p.3 (PDF p.4); restated and proved p.16 (PDF p.17)

import Mathlib
import Definitions.Def_OneOfManyCC_CC
import Definitions.Def_OneOfManyCC_Supplement_DeMorgan
import Definitions.Def_OneOfManyCC_Supplement_Composition

namespace OneOfManyCC.Supplement

open OneOfManyCC

/-- **Theorem 1.7** (constant-density cores for every function).
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.7, p.3 (restated and proved p.16):
"For every nonconstant total g: {0, 1}n → {0, 1}, there is a nonempty S ⊆ {0, 1}n such that, for
every m ≥ 2 and every X ⊆ Sm of relative density at least (1 + 2¹⁻ᵐ)/3, CC(Rg(X)) ≥ D(g) − O(log n)."

**Formalization Note.** The `O(log n)` is one absolute constant `C` chosen before `n` and `g`. One
set `S` serves every `m ≥ 2`. The core is `Sᵐ` (the matrices all of whose rows lie in `S`), and the
relative density is `|X| / |S|ᵐ`, written `|X| ≥ ((1 + 2^(1−m))/3) · |S|ᵐ` in `ℝ`. `D(g)` is
`D (fun x => some (g x))`. Logarithms are base 2. -/
theorem theorem_1_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (g : (Fin n → Bool) → Bool), (∃ x y, g x ≠ g y) →
      ∃ S : Set (Fin n → Bool), S.Nonempty ∧
        ∀ m : ℕ, 2 ≤ m → ∀ X : Set (Um n m), X ⊆ {Z | ∀ i, Z i ∈ S} →
          (1 + (2 : ℝ) ^ (1 - (m : ℤ))) / 3 * (S.ncard : ℝ) ^ m ≤ (X.ncard : ℝ) →
            (D (fun x => some (g x)) : ℝ) - C * Real.logb 2 n ≤ (CC (Rg g X) : ℝ) := by sorry

end OneOfManyCC.Supplement
