-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_66
-- name    : NKtLB.Supplement.theorem_66
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:44:43.026295+00:00
-- url     : https://prove2.me/theorems/3a6ed5a9-7688-4b6c-b974-e5896e46835f
-- title:
--   Theorem 66 (= Theorem 3) — an oracle relative to which SoI fails with linear gap for rKt, pKt, nKt, rnKt, pnKt
-- statement:
--   There are an oracle $O$ and a constant $\varepsilon>0$ such that for every measure $\mu\in\{r\mathrm{Kt},p\mathrm{Kt},n\mathrm{Kt},rn\mathrm{Kt},pn\mathrm{Kt}\}$ and all sufficiently large $n$ there are $x,y\in\{0,1\}^n$ with
--   $$
--   \mu^O(x,y)\ <\ \mu^O(x)+\mu^O(y\mid x)-\varepsilon n .
--   $$
--
--   Here $\mu^O$ is the measure relativized to $O$ (the oracle is given to the universal machine), the randomized measures use success probability $2/3$, and $U$ is an arbitrary valid universal machine. Any proof of worst-case symmetry of information for these measures must therefore be non-relativizing.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: relativized measures $\mu^O$ (Definitions 13–22 defined without oracle; p.22: they 'can easily be generalized') → the oracle $O$ is given to $U$, as in Definitions 11–12 and the base `nKt`; reason: the generalization the paper names
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 66, p.43 (= Theorem 3, p.9)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_rKt
import Definitions.Def_NKtLB_Supplement_pKt
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_Supplement_rnKt
import Definitions.Def_NKtLB_Supplement_pnKt
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **Theorem 66 (= Theorem 3, Strong Failure of SoI in Some Oracle World)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 66, p.43,
restating Theorem 3, p.9): "There exist an oracle `O` and a constant `ε > 0` such that, for every
complexity measure `μ ∈ {rKt, pKt, nKt, rnKt, pnKt}`, the following holds. For all sufficiently large
`n ∈ ℕ`, there exist strings `x, y ∈ {0,1}^n` such that `μ^O(x, y) < μ^O(x) + μ^O(y | x) − ε · n`."

**Formalization Note.** For every valid universal machine `U`; `O` and `ε` are chosen before `μ`
(the threshold may depend on `μ`). The relativized measures give the oracle `O` to `U` (p.22): `rKt`,
`pKt`, `rnKt`, `pnKt` with `λ = 2/3` and the base `nKt` without query bound. -/
theorem theorem_66 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∃ O : Set (List Bool), ∃ ε : ℝ, 0 < ε ∧
      ∀ mu ∈ ({fun x y => rKt U O (2 / 3) x y, fun x y => pKt U O (2 / 3) x y,
          fun x y => nKt U O ⊤ x y [], fun x y => rnKt U O (2 / 3) x y,
          fun x y => pnKt U O (2 / 3) x y} : Set (List Bool → List Bool → ℕ∞)),
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
          toEReal (mu (tupleEnc [x, y]) []) <
            toEReal (mu x []) + toEReal (mu y x) - ((ε * n : ℝ) : EReal) := by sorry

end NKtLB.Supplement
