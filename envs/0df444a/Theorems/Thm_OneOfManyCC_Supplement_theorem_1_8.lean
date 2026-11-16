-- Prove2me | Theorems.Thm_OneOfManyCC_Supplement_theorem_1_8
-- name    : OneOfManyCC.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:24:02.564944+00:00
-- url     : https://prove2.me/theorems/00c1f9a8-917f-433d-8c02-573777542fe6
-- title:
--   Theorem 1.8 — a balanced $g_m$ on $2^{\Theta(m)}$ bits with $\mathrm{CC}(R_{g_m}(X))\le D(g_m)-m/2+\sigma+O(\log m)$ in every core
-- statement:
--   For a Boolean function $g$ on $n$ bits and $X\subseteq(\{0,1\}^n)^m$, let $R_g(X)$ be the restriction of $U_m\diamond\mathrm{KW}_g$ to $X\times X$, and let $D(g)$ be the De Morgan formula depth of $g$. A function is **balanced** if $|g^{-1}(1)|=|g^{-1}(0)|=2^{n-1}$.
--
--   There are absolute constants $c_1,c_2,C>0$ and a threshold $M_0$ such that for every even $m\ge M_0$ there are $n$ with
--   $$2^{c_1m}\le n\le 2^{c_2m}$$
--   and a balanced total function $g_m:\{0,1\}^n\to\{0,1\}$ such that, for every nonempty core $X_0\subseteq(\{0,1\}^n)^m$ and every integer $0\le\sigma\le m-1$, some $X\subseteq X_0$ satisfies
--   $$|X|\ge 2^{-m+\sigma}|X_0|\qquad\text{and}\qquad\mathrm{CC}(R_{g_m}(X))\le D(g_m)-\frac m2+\sigma+C\log_2 m.$$
--
--   So no dense-core bound with density slack $o(m)$ and depth loss $o(m)$ depending only on $m$ holds uniformly in $n$, which refutes the uniform form of Dinur and Meir's Conjecture 9.4.
--
--   **Formalization Note** The function $g_m$ is fixed before the core $X_0$ and $\sigma$. Balanced is stated as $|g^{-1}(1)|=|g^{-1}(0)|$. $\sigma$ is a natural number with $\sigma<m$. Sizes and the bound are compared in $\mathbb R$; $D(g)$ is `D (fun x => some (g x))`.
--
--   Differences from the source:
--   - encoding: for every sufficiently large even m; n = 2^Θ(m); O(log m) → ∃ M₀ ∀ m ≥ M₀ even; absolute 0 < c₁, c₂ with 2^(c₁ m) ≤ n ≤ 2^(c₂ m); one absolute constant C > 0 with Real.logb 2 m; all chosen before m; reason: the asymptotic notation with its constants made explicit
--   - encoding: balanced: |g⁻¹(1)| = |g⁻¹(0)| = 2ⁿ⁻¹ → card {x | g x = true} = card {x | g x = false}; reason: the two counts sum to 2ⁿ, so they are equal iff both are 2ⁿ⁻¹
--   - encoding: integer 0 ≤ σ ≤ m − 1 → σ : ℕ with σ < m; reason: the same values of σ
--   - encoding: D(g) for total g; R_g(X) on X × X → D (fun x => some (g x)); Rg g X on the subtype ↥X; reason: a total function is a partial function with no ∗; the size bound makes X nonempty
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.8, p.4 (PDF p.5); restated and proved p.20 (PDF p.21)

import Mathlib
import Definitions.Def_OneOfManyCC_CC
import Definitions.Def_OneOfManyCC_Supplement_DeMorgan
import Definitions.Def_OneOfManyCC_Supplement_Composition

namespace OneOfManyCC.Supplement

open OneOfManyCC

/-- **Theorem 1.8** (an obstruction at exponentially small density).
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.8, p.4 (restated and proved p.20):
"For every sufficiently large even m, there is a balanced total Boolean function gm on n = 2Θ(m) bits
such that, for every nonempty core X0 ⊆ ({0, 1}n)m and every integer 0 ≤ σ ≤ m − 1, some X ⊆ X0
satisfies |X| ≥ 2−m+σ|X0|, CC(Rgm(X)) ≤ D(gm) − m/2 + σ + O(log m)."

**Formalization Note.** "Sufficiently large" is a threshold `M₀`; "`n = 2^Θ(m)`" is two absolute
constants `0 < c₁, c₂` with `2^(c₁ m) ≤ n ≤ 2^(c₂ m)`; `O(log m)` is one absolute constant `C`. All
four are chosen before `m`; `g` is fixed before the core `X₀` and `σ`. Balanced:
`|g⁻¹(1)| = |g⁻¹(0)|` (both are then `2ⁿ⁻¹`). The integer `0 ≤ σ ≤ m − 1` is `σ : ℕ` with `σ < m`.
Sizes and the bound are compared in `ℝ`; `D(g)` is `D (fun x => some (g x))`. Logarithms are base 2. -/
theorem theorem_1_8 :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧ ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → Even m →
      ∃ (n : ℕ) (g : (Fin n → Bool) → Bool),
        (2 : ℝ) ^ (c₁ * m) ≤ n ∧ (n : ℝ) ≤ (2 : ℝ) ^ (c₂ * m) ∧
        (Finset.univ.filter (fun x => g x = true)).card
          = (Finset.univ.filter (fun x => g x = false)).card ∧
        ∀ X₀ : Set (Um n m), X₀.Nonempty → ∀ σ : ℕ, σ < m →
          ∃ X ⊆ X₀, (2 : ℝ) ^ ((σ : ℤ) - m) * (X₀.ncard : ℝ) ≤ (X.ncard : ℝ) ∧
            (CC (Rg g X) : ℝ)
              ≤ (D (fun x => some (g x)) : ℝ) - (m : ℝ) / 2 + σ + C * Real.logb 2 m := by sorry

end OneOfManyCC.Supplement
