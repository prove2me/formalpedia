-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_59
-- name    : NKtLB.Supplement.theorem_59
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:43:04.811576+00:00
-- url     : https://prove2.me/theorems/e2570d3f-a21b-4e9e-b24a-581bc2898385
-- title:
--   Theorem 59 — worst-case SoI for $pn\mathrm{Kt}$ implies $\mathrm{UNSAT}\notin\mathsf{AMTIME}[2^{\log^d n}]$
-- statement:
--   Suppose **worst-case symmetry of information** holds for $pn\mathrm{Kt}$: there is $c>0$ such that for all large enough $n$ and all $x,y\in\{0,1\}^n$
--   $$
--   pn\mathrm{Kt}(x,y)\ \ge\ pn\mathrm{Kt}(x)+pn\mathrm{Kt}(y\mid x)-\log^c n .
--   $$
--   Then for every real $d\ge1$
--   $$
--   \mathrm{UNSAT}\notin\mathsf{AMTIME}[2^{\log^d n}].
--   $$
--
--   Here $pn\mathrm{Kt}=pn\mathrm{Kt}_{2/3}$ (Definition 22), $\log^c n=(\log_2 n)^c$, UNSAT is the set of encodings of unsatisfiable CNF formulas, and $U$ is an arbitrary valid universal machine. In particular, worst-case SoI for $pn\mathrm{Kt}$ would give $\mathsf{coNP}\not\subseteq\mathsf{AM}$, and hence $\mathsf{NP}\not\subseteq\mathsf{BPP}$. A lower bound would follow from the *validity* of SoI.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: $\mathsf C[T]$ with time $O(T)$ on an unspecified machine model → time $c\cdot T+c$ on the base `Machine`; reason: standard classes, not defined in the paper; same reading as the base `NTIME`
--   - encoding: UNSAT over Boolean formulas under an unspecified encoding (TAUT in Theorem 2) → encodings of unsatisfiable CNF formulas under `CNF.enc`; reason: the paper fixes no encoding (p.22); CNF-UNSAT is the standard coNP-complete language
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 59, p.39

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_SoIAt
import Definitions.Def_NKtLB_Supplement_pnKt
import Definitions.Def_NKtLB_Supplement_UNSAT
import Definitions.Def_NKtLB_Supplement_AMTIME
import Definitions.Def_NKtLB_Supplement_twoPolylog

namespace NKtLB.Supplement

/-- **Theorem 59 (worst-case SoI for pnKt implies `UNSAT ∉ AMTIME[2^{log^d n}]`)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026),
Theorem 59, p.39): "Item 1 implies Item 2 in the following.
1. (Worst-Case Symmetry of Information for pnKt). There exists a constant `c > 0` such that for
all large enough `n ∈ ℕ` and `x, y ∈ {0,1}^n`, `pnKt(x, y) ≥ pnKt(x) + pnKt(y | x) − log^c n`.
2. `UNSAT ∉ AMTIME[2^{log^d n}]` for any `d ≥ 1`."

**Formalization Note.** For every valid universal machine `U`. `pnKt = pnKt_{2/3}` (Definition 22),
unrelativized; `log^c n = (log₂ n)^c`; `d` ranges over the reals `d ≥ 1`; `UNSAT` is over CNF formulas
(`CNF.enc`); `AMTIME[T]` is time `O(T)`. -/
theorem theorem_59 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => pnKt U ∅ (2 / 3) x y) n (Real.logb 2 n ^ c)) →
      ∀ d : ℝ, 1 ≤ d → UNSAT ∉ AMTIME (twoPolylog d) := by sorry

end NKtLB.Supplement
