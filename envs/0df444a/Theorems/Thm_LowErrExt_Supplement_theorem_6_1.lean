-- Prove2me | Theorems.Thm_LowErrExt_Supplement_theorem_6_1
-- name    : LowErrExt.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:36:59.774657+00:00
-- url     : https://prove2.me/theorems/1486ed73-e70e-4107-8166-f94caea3b73d
-- title:
--   Theorem 6.1 — rapid mixing: a coset $V$ of mass $\ge2^{-d}$ with $H_\infty[2^{t-1}X'-2^{t-1}X']\ge n-d$, $t\le C\log(n/d)+C$ (corrected: $d>0$)
-- statement:
--   Let $m\ge2$. There is a constant $C>0$ depending only on $m$ such that the following holds. Let $G$ be a finite abelian group with torsion $m$ (that is, $m\cdot x=0$ for all $x\in G$), let $\mathbf X$ be a random variable on $G$ and let $d>0$. Then there is a coset $V\subseteq G$ with $\Pr[\mathbf X\in V]\ge2^{-d}$ such that, writing $\mathbf X'=\mathbf X|_{\mathbf X\in V}$ and $n=H_0[V]$,
--   $$H_\infty\big[2^{t-1}\mathbf X'-2^{t-1}\mathbf X'\big]\ge n-d\qquad\text{for some integer }t\le C\log(n/d)+C .$$
--   Here $2^{t-1}\mathbf X'-2^{t-1}\mathbf X'$ is the difference of two independent sums of $2^{t-1}$ independent copies of $\mathbf X'$, with $\tfrac12\mathbf X'-\tfrac12\mathbf X':=\mathbf X'$ at $t=0$.
--
--   Every source thus has a dense subsource that mixes to the uniform distribution on its coset after logarithmically many differencing steps; this generalizes Theorem 1.5.
--
--   **Formalization Note** Iterated differences are the published `iterDiff`; $H_\infty$ is the published `minEntropy`; logarithms are base 2 (`Real.logb 2`), and at $n=0$ Lean's $\log 0=0$ applies (see the differences).
--
--   Differences from the source:
--   - correction: for any d ≥ 0 → for any d > 0; reason: at d = 0 the statement is false: G = ℤ/2, Pr[X = 0] = 0.9; Pr[X ∈ V] ≥ 1 forces V = G, n = 1, and every 2^{t−1}X − 2^{t−1}X has Pr[0] = (1 + 0.8^{2^t})/2 > 1/2, so H∞ < 1 = n − d for every t (and log(n/0) is undefined)
--   - correction: t ≤ C log(n/d) + C, with log(0/d) = −∞ when n = 0 → t ≤ C·logb 2 (n/d) + C with logb 2 0 = 0, i.e. t ≤ C when V is a point; reason: with the printed −∞ the statement is false: G = ℤ/2, X the point mass at 0, d = 1/2; V = {0} allows no t, and V = G gives H∞ = 0 < 1 − 1/2; with V a point, X′ is a point mass and H∞ = 0 ≥ −d holds at t = 0
--   - reading: C is a constant depending only on m → ∃ C > 0 depending only on m; reason: a mixing-time bound C log(n/d) + C has a positive constant; a negative C would turn the bound into a lower bound on log(n/d)
-- source:
--   D. Doron, J. Goodman, Low-Error Extractors, STOC 2027 submission (manuscript sha256 43c922d6…), Theorem 6.1, p.37

import Mathlib
import Definitions.Def_FuzzyExtractors_Hamming_Basic
import Definitions.Def_LowErrExt_H2
import Definitions.Def_LowErrExt_condOn
import Definitions.Def_LowErrExt_iterDiff
import Definitions.Def_LowErrExt_IsCoset

namespace LowErrExt.Supplement

open LowErrExt FuzzyExtractors.Hamming

/-- **Theorem 6.1 (Rapid mixing), corrected: `d > 0`.**
Doron, Goodman, *Low-Error Extractors*, STOC 2027 submission (manuscript sha256 43c922d6…),
Theorem 6.1, p.37: "Let X ∼ G, where G is a finite abelian group with torsion m ≥ 2. For any d ≥ 0,
there exists some coset V ⊆ G with Pr[X ∈ V] ≥ 2^{−d} such that if we define X′ := X|_{X∈V}, then
H∞[2^{t−1}X′ − 2^{t−1}X′] ≥ n − d for some t ≤ C log(n/d) + C, where n := H0[V] ≤ H0[G], and C is a
constant depending only on m."

**Formalization Note.** Correction: `d > 0` instead of `d ≥ 0`. At `d = 0`, `log(n/d)` is undefined,
and the statement fails for `G = ℤ/2`, `Pr[X = 0] = 0.9`: `Pr[X ∈ V] ≥ 1` forces `V = G`, `n = 1`,
and every `2^{t−1}X − 2^{t−1}X` has `Pr[0] = (1 + 0.8^{2^t})/2 > 1/2`, so `H∞ < 1 = n − d`.
"Torsion `m`" is `m • x = 0` for all `x`; `C > 0` is chosen after `m` and before `G, X, d`. `t ∈ ℕ`,
`t = 0` meaning `X′` itself (`½X′ − ½X′ := X′`, p.45; published `iterDiff`). `H∞` is the published
`minEntropy`; log base 2 (`Real.logb 2`). When `n = 0` (`V` a point) Lean's `log 0 = 0` reads the
bound as `t ≤ C`; the printed `log(0/d) = −∞` would leave no `t` even though `X′` is then a point
mass with `H∞ = 0 ≥ −d`. -/
theorem theorem_6_1 (m : ℕ) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (G : Type) [AddCommGroup G] [Fintype G], (∀ x : G, m • x = 0) →
        ∀ (X : PMF G) (d : ℝ), 0 < d →
          ∃ V : Set G, IsCoset V ∧ (2 : ℝ) ^ (-d) ≤ probOf X V ∧
            ∃ t : ℕ, (t : ℝ) ≤ C * Real.logb 2 (H0 V / d) + C ∧
              H0 V - d ≤ minEntropy (iterDiff t (condOn X V)) := by sorry

end LowErrExt.Supplement
