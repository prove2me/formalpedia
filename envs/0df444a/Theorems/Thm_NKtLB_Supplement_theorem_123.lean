-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_123
-- name    : NKtLB.Supplement.theorem_123
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:46:43.776122+00:00
-- url     : https://prove2.me/theorems/d7c16af7-2f5b-47e6-abf2-b619d7e9e334
-- title:
--   Theorem 123 — Gap-MnKtP$[0.6n,0.9n]\notin\mathsf{DTIME}[2^{\varepsilon n}]$
-- statement:
--   **Hardness of approximating $n\mathrm{Kt}$.** There is $\varepsilon>0$ such that
--   $$
--   \text{Gap-MnKtP}[0.6n,\,0.9n]\notin\mathsf{DTIME}[2^{\varepsilon n}],
--   $$
--   i.e. no deterministic $2^{O(\varepsilon n)}$-time algorithm accepts every $x$ with $n\mathrm{Kt}(x)\le 0.6|x|$ and rejects every $x$ with $n\mathrm{Kt}(x)\ge 0.9|x|$.
--
--   Here $n\mathrm{Kt}$ is taken with respect to an arbitrary valid universal machine $U$. The paper derives this as a corollary of the "moreover" part of Theorem 8 and uses it to refute conditional symmetry of information for $n\mathrm{Kt}$ (Theorem 10).
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - reading: $\mathsf C[T]$ with time $O(T)$ on an unspecified machine model → time $c\cdot T+c$ on the base `Machine`; reason: standard classes, not defined in the paper; same reading as the base `NTIME`
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 123, p.90

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_GapMnKtP
import Definitions.Def_NKtLB_Supplement_PromiseIn
import Definitions.Def_NKtLB_Supplement_DTIME
import Definitions.Def_NKtLB_expBound

namespace NKtLB.Supplement

/-- **Theorem 123 (Hardness of Approximating nKt; Corollary of Theorem 8)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 123, p.90):
"There exists `ε > 0` such that the following result holds: `Gap-MnKtP[0.6n, 0.9n] ∉ DTIME[2^{ε·n}]`."

**Formalization Note.** For every valid universal machine `U`. Promise non-membership is
`¬ PromiseIn` (p.10, p.12); `Gap-MnKtP` has NO side `nKt(x) ≥ 0.9|x|` (p.24); `2^{εn}` is the base
`expBound ε`; `DTIME[T]` is deterministic time `O(T)`. -/
theorem theorem_123 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∃ ε : ℝ, 0 < ε ∧
      ¬ PromiseIn (GapMnKtP U (fun n => 6 / 10 * n) (fun n => 9 / 10 * n))
        (DTIME (expBound ε)) := by sorry

end NKtLB.Supplement
