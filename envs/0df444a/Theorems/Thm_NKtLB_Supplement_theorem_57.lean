-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_57
-- name    : NKtLB.Supplement.theorem_57
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:41:46.307328+00:00
-- url     : https://prove2.me/theorems/c4725a20-a370-4f60-8e4c-f1b27a0bf952
-- title:
--   Theorem 57 — semi-symmetry of information for $rnK$
-- statement:
--   There is a polynomial $p$ such that for all sufficiently large $n,t\in\mathbb N$ with $t\ge 4n$ and all $x,y\in\{0,1\}^n$,
--   $$
--   pK^t(x,y)\ \ge\ rnK^{p(t)}(x)+rnK^{p(t)}(y\mid x)-\log p(t)-\log^3 p(n).
--   $$
--
--   Here $pK^t=pK^t_{2/3}$ (Definition 15), $rnK^t=rnK^t_{2/3}$ (Definition 19), $\log^3 p(n)=(\log_2 p(n))^3$, and $U$ is an arbitrary valid universal machine. This is the analogue of Theorem 55 for randomized nondeterministic complexity, and the step behind Theorem 58.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - encoding: a polynomial $p$ → `p : Polynomial ℕ`; reason: a polynomial with natural coefficients covers every polynomial upper bound used
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 57, p.38

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_pKtime
import Definitions.Def_NKtLB_Supplement_rnKtime
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **Theorem 57 (semi-SoI for rnK)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 57, p.38): "There exists a polynomial `p` such
that, for all sufficiently large `n, t ∈ ℕ` with `t ≥ 4n`, the following holds. For all
`x, y ∈ {0,1}^n`, `pK^t(x, y) ≥ rnK^{p(t)}(x) + rnK^{p(t)}(y | x) − log p(t) − log^3 p(n)`."

**Formalization Note.** For every valid universal machine `U`. `pK^t = pK^t_{2/3}` (Definition 15),
`rnK^t = rnK^t_{2/3}` (Definition 19), unrelativized; `log^3 p(n) = (log₂ p(n))^3`. Quantifiers as in
Theorem 55. -/
theorem theorem_57 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∃ p : Polynomial ℕ, ∃ N : ℕ, ∀ n t : ℕ, N ≤ n → 4 * n ≤ t →
      ∀ x y : List Bool, x.length = n → y.length = n →
        toEReal (rnKtime U ∅ (2 / 3) (p.eval t) x []) + toEReal (rnKtime U ∅ (2 / 3) (p.eval t) y x)
            - ((Real.logb 2 ((p.eval t : ℕ) : ℝ) + Real.logb 2 ((p.eval n : ℕ) : ℝ) ^ 3 : ℝ) : EReal)
          ≤ toEReal (pKtime U ∅ (2 / 3) t (tupleEnc [x, y]) []) := by sorry

end NKtLB.Supplement
