-- Prove2me | Theorems.Thm_OneOfManyCC_Supplement_theorem_6_6
-- name    : OneOfManyCC.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:24:31.461667+00:00
-- url     : https://prove2.me/theorems/f0d5c2aa-32b3-422c-a381-0016573b887c
-- title:
--   Theorem 6.6 — for random $g$, $\mathrm{CC}(R_g(X))\ge n-O(\log n)$ for every $X\subseteq U_m$ of density $\ge 2^{1-m}$, all $m\le n^2$
-- statement:
--   Let $g:\{0,1\}^n\to\{0,1\}$ be a uniformly random Boolean function, $U_m=(\{0,1\}^n)^m$, and for $X\subseteq U_m$ let $R_g(X)$ be the restriction of $U_m\diamond\mathrm{KW}_g$ to $X\times X$: on $A,B\in X$ the players output a cell $(i,j)$ with $A_{i,j}\ne B_{i,j}$, or reject when $g^m(A)=g^m(B)$.
--
--   There is an absolute constant $C>0$ such that, with probability $1-o(1)$ as $n\to\infty$, the function $g$ satisfies, for every $1\le m\le n^2$ and every $X\subseteq U_m$ of relative density at least $2^{1-m}$, i.e. $|X|\ge 2^{1-m}\cdot 2^{mn}$,
--   $$\mathrm{CC}(R_g(X))\ge n-C\log_2 n.$$
--
--   This is the dense-restriction bound behind Theorem 1.6. The threshold $2^{1-m}$ is tight up to a factor $2$: on a set where $g^m$ is constant the players reject without communicating.
--
--   **Formalization Note** "With probability $1-o(1)$" is: the fraction of the $2^{2^n}$ functions $g$ satisfying the event (for all $m$ and all $X$ simultaneously) tends to $1$. The relative density is taken in the core $U_m$, $|X|\ge 2^{1-m}|U_m|$, compared in $\mathbb R$.
--
--   Differences from the source:
--   - encoding: with probability 1 − o(1), for a uniformly random g → Tendsto (fun n => probUniform n event) atTop (𝓝 1); reason: the probability of the event under the uniform distribution on the 2^(2ⁿ) functions tends to 1 as n → ∞
--   - encoding: O(log n) → one absolute constant C > 0 chosen before every type and parameter, with base-2 logarithms (Real.logb 2); reason: the paper's O(·) hides an absolute constant; logarithms are base 2 (§3)
--   - encoding: X ⊆ U_m of relative density at least 2¹⁻ᵐ → 2^(1−m) · |U_m| ≤ |X| in ℝ; reason: the core is U_m (§6, p.12); the density bound makes X nonempty
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 6.6, p.18 (PDF p.19)

import Mathlib
import Definitions.Def_OneOfManyCC_CC
import Definitions.Def_OneOfManyCC_Supplement_Composition
import Definitions.Def_OneOfManyCC_Supplement_UniformProb

namespace OneOfManyCC.Supplement

open OneOfManyCC Filter Topology

/-- **Theorem 6.6** (Dense restrictions of random functions).
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Theorem 6.6, p.18:
"With probability 1 − o(1), a uniformly random g: {0, 1}n → {0, 1} satisfies, for every
1 ≤ m ≤ n² and every X ⊆ Um of relative density at least 2¹⁻ᵐ, CC(Rg(X)) ≥ n − O(log n)."

**Formalization Note.** The `O(log n)` is one absolute constant `C` chosen before `n`; "with
probability `1 − o(1)`" is: the fraction of the `2^(2ⁿ)` functions `g` satisfying the event tends
to `1` as `n → ∞`. The event is simultaneous over all `m` and `X`. The relative density is in the
core `U_m` (§6, p.12), `|X| ≥ 2^(1−m) · |U_m|`, computed in `ℝ`. Logarithms are base 2. -/
theorem theorem_6_6 :
    ∃ C : ℝ, 0 < C ∧ Tendsto (fun n : ℕ => probUniform n (fun g =>
      ∀ m : ℕ, 1 ≤ m → m ≤ n ^ 2 → ∀ X : Set (Um n m),
        (2 : ℝ) ^ (1 - (m : ℤ)) * (Fintype.card (Um n m) : ℝ) ≤ (X.ncard : ℝ) →
          (n : ℝ) - C * Real.logb 2 n ≤ (CC (Rg g X) : ℝ))) atTop (𝓝 1) := by sorry

end OneOfManyCC.Supplement
