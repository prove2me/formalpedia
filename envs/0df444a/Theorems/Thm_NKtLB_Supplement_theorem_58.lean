-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_58
-- name    : NKtLB.Supplement.theorem_58
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:42:19.338485+00:00
-- url     : https://prove2.me/theorems/d8c372a1-5831-44fa-a7d9-bd4873361ec1
-- title:
--   Theorem 58 — average-case symmetry of information for rnKt
-- statement:
--   For every polynomial-time samplable distribution family $\{D_n\}_{n\in\mathbb N}$ supported over $\{0,1\}^n\times\{0,1\}^n$ there is a constant $c>0$ such that for all large enough $n,k\in\mathbb N$
--   $$
--   \Pr_{(x,y)\sim D_n}\Bigl[\,rn\mathrm{Kt}(x,y)\ \ge\ rn\mathrm{Kt}(x)+rn\mathrm{Kt}(y\mid x)-c\log^3 n-\log k\,\Bigr]\ \ge\ 1-\frac1k .
--   $$
--
--   Here $rn\mathrm{Kt}=rn\mathrm{Kt}_{2/3}$ (Definition 20), $\log^3 n=(\log_2 n)^3$, and $U$ is an arbitrary valid universal machine. This is the second part of Theorem 1: SoI holds on average for $rn\mathrm{Kt}$, whereas for $r\mathrm{Kt}$ it fails on average if one-way functions exist.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: a polynomial-time samplable family $\{D_n\}$ → a sampler $(A,q)$ with time and randomness $n^q+q$; reason: standard notion, not defined in the paper
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 58, p.38

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_rnKt
import Definitions.Def_NKtLB_Supplement_IsPolySampler
import Definitions.Def_NKtLB_Supplement_sampProb
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **Theorem 58 (average-case SoI for rnKt)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 58, p.38; the second part of Theorem 1,
p.8): "For every polynomial-time samplable distribution family `{D_n}_{n∈ℕ}` supported over
`{0,1}^n × {0,1}^n`, there exists a constant `c > 0` such that for all large enough `n, k ∈ ℕ`,
`Pr_{(x,y)∼D_n}[ rnKt(x, y) ≥ rnKt(x) + rnKt(y | x) − c · log^3 n − log k ] ≥ 1 − 1/k`."

**Formalization Note.** As Theorem 56, with `rnKt = rnKt_{2/3}` (Definition 20) on all three terms;
`log^3 n = (log₂ n)^3`. -/
theorem theorem_58 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∀ (A : Machine) (q : ℕ), IsPolySampler A q → ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → N ≤ k →
      1 - 1 / (k : ℝ) ≤ sampProb A q n (fun x y =>
        toEReal (rnKt U ∅ (2 / 3) x []) + toEReal (rnKt U ∅ (2 / 3) y x)
            - ((c * Real.logb 2 n ^ 3 + Real.logb 2 k : ℝ) : EReal)
          ≤ toEReal (rnKt U ∅ (2 / 3) (tupleEnc [x, y]) [])) := by sorry

end NKtLB.Supplement
