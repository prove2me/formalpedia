-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_56
-- name    : NKtLB.Supplement.theorem_56
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:41:05.41742+00:00
-- url     : https://prove2.me/theorems/90bc5e8d-9a50-4090-97f4-5a5e74ef1ea1
-- title:
--   Theorem 56 — average-case symmetry of information for pnKt
-- statement:
--   For every polynomial-time samplable distribution family $\{D_n\}_{n\in\mathbb N}$ supported over $\{0,1\}^n\times\{0,1\}^n$ there is a constant $c>0$ such that for all large enough $n,k\in\mathbb N$
--   $$
--   \Pr_{(x,y)\sim D_n}\Bigl[\,pn\mathrm{Kt}(x,y)\ \ge\ p\mathrm{Kt}(x)+pn\mathrm{Kt}(y\mid x)-c\log n-\log k\,\Bigr]\ \ge\ 1-\frac1k .
--   $$
--
--   Here $p\mathrm{Kt}=p\mathrm{Kt}_{2/3}$ and $pn\mathrm{Kt}=pn\mathrm{Kt}_{2/3}$ (Definitions 16 and 22), $\log=\log_2$, and $U$ is an arbitrary valid universal machine. This is the first part of Theorem 1 in a stronger form ($p\mathrm{Kt}(x)$ in place of $pn\mathrm{Kt}(x)$). It contrasts with the randomized setting, where one-way functions make SoI fail on average for $p\mathrm{Kt}$.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: a polynomial-time samplable family $\{D_n\}$ over $\{0,1\}^n\times\{0,1\}^n$ → a sampler $(A,q)$: on $1^n$ and $n^q+q$ random bits it halts within $n^q+q$ steps with a pair in $\{0,1\}^n\times\{0,1\}^n$; reason: standard notion, not defined in the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 56, p.37

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_pKt
import Definitions.Def_NKtLB_Supplement_pnKt
import Definitions.Def_NKtLB_Supplement_IsPolySampler
import Definitions.Def_NKtLB_Supplement_sampProb
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **Theorem 56 (average-case SoI for pnKt)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 56, p.37; the stronger form of the first
part of Theorem 1, p.8): "For every polynomial-time samplable distribution family `{D_n}_{n∈ℕ}`
supported over `{0,1}^n × {0,1}^n`, there exists a constant `c > 0` such that for all large enough
`n, k ∈ ℕ`, `Pr_{(x,y)∼D_n}[ pnKt(x, y) ≥ pKt(x) + pnKt(y | x) − c · log n − log k ] ≥ 1 − 1/k`."

**Formalization Note.** For every valid universal machine `U`. A samplable family is a sampler
`(A, q)` with `IsPolySampler A q` (time and randomness `n^q + q`), and `Pr_{D_n}` is `sampProb A q n`.
`pKt = pKt_{2/3}`, `pnKt = pnKt_{2/3}` (Definitions 16, 22), unrelativized. "For all large enough
`n, k`" is `∃ N, ∀ n ≥ N, ∀ k ≥ N`; `c` depends on the family only. `log = log₂`. -/
theorem theorem_56 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∀ (A : Machine) (q : ℕ), IsPolySampler A q → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → N ≤ k →
      1 - 1 / (k : ℝ) ≤ sampProb A q n (fun x y =>
        toEReal (pKt U ∅ (2 / 3) x []) + toEReal (pnKt U ∅ (2 / 3) y x)
            - ((c * Real.logb 2 n + Real.logb 2 k : ℝ) : EReal)
          ≤ toEReal (pnKt U ∅ (2 / 3) (tupleEnc [x, y]) [])) := by sorry

end NKtLB.Supplement
