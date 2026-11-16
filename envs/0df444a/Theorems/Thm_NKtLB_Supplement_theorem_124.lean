-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_124
-- name    : NKtLB.Supplement.theorem_124
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:47:32.819194+00:00
-- url     : https://prove2.me/theorems/39c65b34-0a8a-4075-ac59-445659b6c333
-- title:
--   Theorem 124 — $\mathrm{Kt}^{\|2\,\mathrm{SAT}}(x,y)<n\mathrm{Kt}(x)+n\mathrm{Kt}(y\mid x)-\varepsilon n$
-- statement:
--   There is a constant $\varepsilon>0$ such that for every large enough $n$ there are $x,y\in\{0,1\}^n$ with
--   $$
--   \mathrm{Kt}^{\|2\,\mathrm{SAT}}(x,y)\ <\ n\mathrm{Kt}(x)+n\mathrm{Kt}(y\mid x)-\varepsilon n ,
--   $$
--   where $\mathrm{Kt}^{\|d\,O}$ is Levin–Kolmogorov complexity in which the universal machine may query $O$ with up to $d$ levels of adaptivity.
--
--   Symmetry of information fails in a hybrid setting: Kt with two rounds of SAT queries on the left, nondeterministic complexity on the right. Since $n\mathrm{Kt}$ is within a constant factor of Kt with one round of SAT queries, the result isolates adaptivity as the obstacle to extending Ronneburger's argument to $n\mathrm{Kt}$.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: oracle calls with up to $d$ levels of adaptivity in $\mathrm{Kt}^{\|d\,O}$ (p.96) → the first $t$ steps of $U$ split into at most $d$ rounds (`AdaptRounds` with $d=2$), the queries of each round fixed before any answer of that round; reason: the paper gives no formal definition; this is the semantic one
--   - encoding: the oracle SAT → encodings of satisfiable CNF formulas under `CNF.enc`; reason: the paper fixes no encoding (p.22)
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Appendix A, Theorem 124, p.96

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_KtPar
import Definitions.Def_NKtLB_Supplement_SAT
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **Theorem 124 (failure of SoI in a hybrid setting)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Appendix A, Theorem 124, p.96): "There
is a constant `ε > 0` such that for every large enough `n ∈ ℕ`, there exist strings `x, y ∈ {0,1}^n`
such that `Kt^{∥2 SAT}(x, y) < nKt(x) + nKt(y | x) − εn`. Here, for an oracle `O` and a constant
`d ∈ ℕ`, `Kt^{∥d O}` refers to the complexity measure `Kt` wherein the universal machine may make
oracle calls to `O` with up to `d` levels of adaptivity."

**Formalization Note.** For every valid universal machine `U`. `Kt^{∥2 SAT}` is `KtPar U SAT 2` (two
rounds of queries to SAT over CNF encodings); `nKt` is the base `nKt` with `O = ∅`; `(x, y)` is
`tupleEnc [x, y]`. -/
theorem theorem_124 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
      toEReal (KtPar U SAT 2 (tupleEnc [x, y]) []) <
        toEReal (nKt U ∅ ⊤ x [] []) + toEReal (nKt U ∅ ⊤ y x []) - ((ε * n : ℝ) : EReal) := by sorry

end NKtLB.Supplement
