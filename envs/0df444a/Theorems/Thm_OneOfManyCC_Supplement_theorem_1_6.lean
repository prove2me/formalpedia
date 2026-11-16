-- Prove2me | Theorems.Thm_OneOfManyCC_Supplement_theorem_1_6
-- name    : OneOfManyCC.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:22:35.040542+00:00
-- url     : https://prove2.me/theorems/9a188f5e-fd6b-44c3-98e4-e663444bd958
-- title:
--   Theorem 1.6 — for random $g$, $\mathrm{CC}(U_m\diamond\mathrm{KW}_g)\ge m+n-O(\log n)\ge m+D(g)-O(\log n)$ for all $m\le n^2$
-- statement:
--   Let $g:\{0,1\}^n\to\{0,1\}$ be a uniformly random Boolean function, and for $m\ge1$ let $U_m\diamond\mathrm{KW}_g$ be the composition of the universal relation on $m$ bits with the Karchmer–Wigderson game of $g$: Alice and Bob receive $A,B\in(\{0,1\}^n)^m$ and must output a cell $(i,j)$ with $A_{i,j}\ne B_{i,j}$, or reject when $g^m(A)=g^m(B)$. Let $D(g)$ be the De Morgan formula depth of $g$.
--
--   There are absolute constants $C_1,C_2>0$ such that, with probability $1-o(1)$ as $n\to\infty$, the function $g$ satisfies, simultaneously for all $1\le m\le n^2$,
--   $$\mathrm{CC}(U_m\diamond\mathrm{KW}_g)\;\ge\;m+n-C_1\log_2 n\;\ge\;m+D(g)-C_2\log_2 n.$$
--
--   This is a near-optimal composition lower bound with the universal relation for almost every inner function: the natural protocol uses $m+D(g)+O(\log m)$ bits.
--
--   **Formalization Note** "With probability $1-o(1)$" is: the fraction of the $2^{2^n}$ functions $g$ satisfying the event (both inequalities, for every $1\le m\le n^2$) tends to $1$ as $n\to\infty$. $D(g)$ is `D (fun x => some (g x))`.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1) as n → ∞, for a uniformly random g → Tendsto (fun n => probUniform n event) atTop (𝓝 1); reason: the probability of the event under the uniform distribution on the 2^(2ⁿ) functions tends to 1
--   - encoding: the two O(log n) terms of the chain → two absolute constants C₁, C₂ > 0 chosen before n, with base-2 logarithms; reason: each O(·) is its own absolute constant (standard convention); one constant on both sides would assert n ≥ D(g), which the paper does not claim
--   - encoding: outputs of U_m ⋄ KW_g: a cell (i, j) or reject → Option (Fin m × Fin n), none = reject; reason: the same answers, 0-based
--   - encoding: D(g) for total g → D (fun x => some (g x)); reason: a total function is a partial function with no ∗
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.6, p.3 (PDF p.4); restated and proved p.18 (PDF p.19)

import Mathlib
import Definitions.Def_OneOfManyCC_CC
import Definitions.Def_OneOfManyCC_Supplement_DeMorgan
import Definitions.Def_OneOfManyCC_Supplement_Composition
import Definitions.Def_OneOfManyCC_Supplement_UniformProb

namespace OneOfManyCC.Supplement

open OneOfManyCC Filter Topology

/-- **Theorem 1.6.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 1.6, p.3 (restated and proved p.18):
"With probability 1 − o(1) as n → ∞, a uniformly random g: {0, 1}n → {0, 1} satisfies, for all
1 ≤ m ≤ n², CC(Um ⋄ KWg) ≥ m + n − O(log n) ≥ m + D(g) − O(log n)."

**Formalization Note.** The two `O(log n)` terms are two absolute constants `C₁`, `C₂` chosen
before `n` (one constant on both sides would assert `n ≥ D(g)`). "With probability `1 − o(1)`":
the fraction of the `2^(2ⁿ)` functions satisfying the event tends to `1`. Both inequalities of the
chain are inside the event, for all `1 ≤ m ≤ n²` simultaneously. `D(g)` is the De Morgan depth of
the total `g`, `D (fun x => some (g x))`. Logarithms are base 2. -/
theorem theorem_1_6 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ Tendsto (fun n : ℕ => probUniform n (fun g =>
      ∀ m : ℕ, 1 ≤ m → m ≤ n ^ 2 →
        (m : ℝ) + n - C₁ * Real.logb 2 n ≤ (CC (UKW (m := m) g) : ℝ) ∧
          (m : ℝ) + (D (fun x => some (g x)) : ℝ) - C₂ * Real.logb 2 n
            ≤ (m : ℝ) + n - C₁ * Real.logb 2 n)) atTop (𝓝 1) := by sorry

end OneOfManyCC.Supplement
