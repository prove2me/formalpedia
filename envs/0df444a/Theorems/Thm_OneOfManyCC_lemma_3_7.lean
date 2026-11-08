-- Prove2me | Theorems.Thm_OneOfManyCC_lemma_3_7
-- name    : OneOfManyCC.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:52:44.435439+00:00
-- url     : https://prove2.me/theorems/9d61dba3-acaa-4beb-8cdf-1ec1abc87268
-- title:
--   Lemma 3.7 (Valiant) — from $1/2+\varepsilon$ correct at each point to one formula correct everywhere
-- statement:
--   Let $\mathcal Z$ be a finite set, let $f:\mathcal Z\to\{0,1\}$, let $\mathcal F$ be a set of functions $\mathcal Z\to\{0,1\}$, and let $0<\varepsilon\le 1/2$. Suppose a distribution $\Lambda$ over formulas of depth at most $d$ with AND and OR gates and leaves from $\mathcal F$ satisfies
--
--   $$\Pr_{H\sim\Lambda}[H(z)=f(z)]\ge\frac12+\varepsilon\quad\text{for every }z\in\mathcal Z.$$
--
--   Then some formula $H^*$ with leaves from $\mathcal F$ and depth
--
--   $$d+O\bigl(\log(1/\varepsilon)+\log\log|\mathcal Z|\bigr)$$
--
--   satisfies $H^*(z)=f(z)$ for every $z\in\mathcal Z$. The constant in $O(\cdot)$ is absolute. Gates are AND and OR only, so the amplification does not leave the given leaf set.
--
--   Differences from the source:
--   - encoding: a distribution $\Lambda$ over formulas of depth at most $d$ → a finite family `H : ι → Formula F` with weights `w ∈ stdSimplex ℝ ι`; reason: for finite $\mathcal Z$ there are finitely many such formulas, so every such distribution has finite support
--   - encoding: $O(\cdot)$ → one constant $C>0$ quantified before all parameters; reason: the paper's $O(\cdot)$ is absolute
--   - encoding: $\log$ inside $O(\cdot)$ and $\lceil\log_2\cdot\rceil$ → `Real.logb 2` and `Nat.clog 2`; reason: the paper's logarithms are base 2; `Nat.clog 2 m` is $\lceil\log_2 m\rceil$ for $m\ge1$ and `Real.logb 2 0 = 0`
--   - encoding: a distribution on a finite set → a point of `stdSimplex ℝ X`, with $\mu(E)$ as `mass μ E`; reason: nonnegative weights summing to one; the probability of an event is the sum of its weights
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), Lemma 3.7, p.8

import Mathlib
import Definitions.Def_OneOfManyCC_Formula
import Definitions.Def_OneOfManyCC_mass

namespace OneOfManyCC

/-- **Lemma 3.7 (Valiant), majority amplification.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), Lemma 3.7, p.8:
"Let Z be a finite set, let f : Z → {0, 1}, let F be a set of functions Z → {0, 1}, and let
0 < ε ≤ 1/2. If a distribution Λ over formulas of depth at most d with AND and OR gates and leaves
from F satisfies Pr_{H∼Λ}[H(z) = f(z)] ≥ 1/2 + ε for every z ∈ Z, then some formula H∗ of depth
d + O(log(1/ε) + log log |Z|) with leaves from F satisfies H∗(z) = f(z) for every z ∈ Z."

**Formalization Note.** The constant is absolute: `∃ C` stands before every parameter. `Λ` is a finite
family `H : ι → Formula F` with weights `w ∈ stdSimplex ℝ ι`; this loses nothing, since for finite `Z`
there are finitely many formulas of depth at most `d`. Logarithms are base `2`. For `|Z| ≤ 2` the
term `log₂ log₂ |Z|` is `0` in Lean, and `log₂(1/ε) ≥ 1`. -/
theorem lemma_3_7 :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z : Type) [Fintype Z] (f : Z → Bool) (F : Set (Z → Bool)) (ε : ℝ) (d : ℕ)
      (ι : Type) [Fintype ι] (w : ι → ℝ) (H : ι → Formula F),
      0 < ε → ε ≤ 1 / 2 → w ∈ stdSimplex ℝ ι → (∀ i, (H i).depth ≤ d) →
      (∀ z, 1 / 2 + ε ≤ mass w {i | (H i).eval (fun l => l.1) z = f z}) →
      ∃ Hstar : Formula F,
        (Hstar.depth : ℝ) ≤
          d + C * (Real.logb 2 (1 / ε) + Real.logb 2 (Real.logb 2 (Fintype.card Z))) ∧
        ∀ z, Hstar.eval (fun l => l.1) z = f z := by sorry

end OneOfManyCC
