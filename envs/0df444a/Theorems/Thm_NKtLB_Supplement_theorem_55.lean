-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_55
-- name    : NKtLB.Supplement.theorem_55
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:40:15.967508+00:00
-- url     : https://prove2.me/theorems/48d9e548-df02-42f1-84a7-ec051ff462f4
-- title:
--   Theorem 55 — semi-symmetry of information for $pnK$
-- statement:
--   There is a polynomial $p$ such that for all sufficiently large $n,t\in\mathbb N$ with $t\ge 4n$ and all $x,y\in\{0,1\}^n$,
--   $$
--   pK^t(x,y)\ \ge\ pK^{p(t)}(x)+pnK^{p(t)}(y\mid x)-\log p(t).
--   $$
--
--   Here $pK^t=pK^t_{2/3}$ is the probabilistic $t$-time-bounded Kolmogorov complexity (Definition 15), $pnK^t=pnK^t_{2/3}$ its nondeterministic counterpart (Definition 21), $\log=\log_2$, and $U$ is an arbitrary valid universal machine.
--
--   The joint complexity is at least the deterministic complexity of $x$ plus the *nondeterministic* conditional complexity of $y$ given $x$, up to a polynomial slowdown and a logarithmic loss. This is the step from which average-case symmetry of information for $pn\mathrm{Kt}$ (Theorem 56) is derived.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - encoding: a polynomial $p$ → `p : Polynomial ℕ`, evaluated at $t$; reason: a polynomial with natural coefficients covers every polynomial upper bound used
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 55, p.36

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_pKtime
import Definitions.Def_NKtLB_Supplement_pnKtime
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **Theorem 55 (semi-SoI for pnK)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 55, p.36): "There exists a polynomial `p` such
that, for all sufficiently large `n, t ∈ ℕ` with `t ≥ 4n`, the following holds. For all
`x, y ∈ {0,1}^n`, `pK^t(x, y) ≥ pK^{p(t)}(x) + pnK^{p(t)}(y | x) − log p(t)`."

**Formalization Note.** For every valid universal machine `U`. `pK^t = pK^t_{2/3}` (Definition 15),
`pnK^t = pnK^t_{2/3}` (Definition 21), unrelativized; `(x, y)` is `tupleEnc [x, y]`. A polynomial is a
`Polynomial ℕ`; "sufficiently large `n, t` with `t ≥ 4n`" is `∃ N, ∀ n ≥ N, ∀ t ≥ 4n` (`t ≥ 4n ≥ N`).
`log = log₂`. -/
theorem theorem_55 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∃ p : Polynomial ℕ, ∃ N : ℕ, ∀ n t : ℕ, N ≤ n → 4 * n ≤ t →
      ∀ x y : List Bool, x.length = n → y.length = n →
        toEReal (pKtime U ∅ (2 / 3) (p.eval t) x []) + toEReal (pnKtime U ∅ (2 / 3) (p.eval t) y x)
            - ((Real.logb 2 ((p.eval t : ℕ) : ℝ) : ℝ) : EReal)
          ≤ toEReal (pKtime U ∅ (2 / 3) t (tupleEnc [x, y]) []) := by sorry

end NKtLB.Supplement
