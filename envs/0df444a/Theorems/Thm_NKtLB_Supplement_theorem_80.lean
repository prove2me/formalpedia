-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_80
-- name    : NKtLB.Supplement.theorem_80
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:45:30.699192+00:00
-- url     : https://prove2.me/theorems/8467b010-7247-48c3-a77d-a7684d7a324f
-- title:
--   Theorem 80 — SoI for $n\mathrm{Kt}$ implies $\mathsf{EXP}^{\|\mathsf{NP}}\subseteq\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly}$
-- statement:
--   Assume $n\mathrm{Kt}$ satisfies symmetry of information with logarithmic error: there is $c>0$ such that for all strings $x,y$ (of any lengths)
--   $$
--   n\mathrm{Kt}(x,y)\ \ge\ n\mathrm{Kt}(x)+n\mathrm{Kt}(y\mid x)-c\log(|x|+|y|).\qquad(12)
--   $$
--   Then
--   $$
--   \mathsf{EXP}^{\|\mathsf{NP}}\subseteq\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly},
--   $$
--   where $\|\mathsf{NP}$ denotes non-adaptive access to an NP oracle.
--
--   Here $n\mathrm{Kt}$ is the nondeterministic Levin–Kolmogorov complexity of the base mission, $rn\mathrm{Kt}=rn\mathrm{Kt}_{2/3}$, $pn\mathrm{Kt}=pn\mathrm{Kt}_{2/3}$, and all measures are taken with respect to an arbitrary valid universal machine $U$. Unlike Theorem 4(ii), the hypothesis (12) covers strings $x,y$ of different lengths, with error measured in $|x|+|y|$.
--
--   **Formalization Note** Lean requires (12) only for $|x|+|y|\ge N$, for some $N$.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: $\mathsf C[T]$ with time $O(T)$ on an unspecified machine model → time $c\cdot T+c$ on the base `Machine`; reason: standard classes, not defined in the paper; same reading as the base `NTIME`
--   - reading: non-adaptive (parallel) oracle access $\|$ → one round of `AdaptRounds` on every input and random string; reason: the paper gives no formal definition; this is the semantic one
--   - reading: oracle class NP in $\mathsf C^{\mathsf{NP}}$ → union over oracles $A\in\mathsf{NP}$; reason: standard meaning of relativization to a class
--   - generalization: Eq. (12) for all strings $x,y$ → Eq. (12) for all $x,y$ with $|x|+|y|\ge N$, for some $N$; reason: a weaker hypothesis: the printed one is the case $N=0$; at $|x|+|y|\le1$ the printed error $c\log(|x|+|y|)$ is $0$ or undefined and 'logarithmic error' does not intend exact additivity there
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 80, p.51, Eq. (12)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_NKtLB_Supplement_NP
import Definitions.Def_NKtLB_Supplement_EXPPar
import Definitions.Def_NKtLB_Supplement_NPpoly
import Definitions.Def_NKtLB_Supplement_coNPpoly

namespace NKtLB.Supplement

/-- **Theorem 80 (SoI for nKt ⇒ `EXP^{∥NP} ⊆ NP/poly ∩ coNP/poly`)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 80, p.51):
"Assume that nKt satisfies symmetry of information with logarithmic error, i.e., there exists a
constant `c > 0` such that for all strings `x, y`,
`nKt(x, y) ≥ nKt(x) + nKt(y | x) − c log(|x| + |y|)`. (12)
Then `EXP^{∥NP} ⊆ NP/poly ∩ coNP/poly`."

**Formalization Note.** For every valid universal machine `U`. The hypothesis is ((12)) for all
strings `x, y` of any lengths with `|x| + |y| ≥ N` for some `N`: for `|x| + |y| ≤ 1` the printed error
`c log(|x| + |y|)` is `0` or undefined and ((12)) would demand exact additivity on the empty and
one-bit strings, which "logarithmic error" does not intend; the printed hypothesis is the case
`N = 0`. `nKt` is the base `nKt` with `O = ∅`;
`EXP^{∥NP} = ⋃_{A ∈ NP} EXP^{∥A}` (non-adaptive queries). -/
theorem theorem_80 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ x y : List Bool, N ≤ x.length + y.length →
      toEReal (nKt U ∅ ⊤ x [] []) + toEReal (nKt U ∅ ⊤ y x [])
          - ((c * Real.logb 2 (x.length + y.length) : ℝ) : EReal)
        ≤ toEReal (nKt U ∅ ⊤ (tupleEnc [x, y]) [] [])) →
      {L | ∃ A ∈ NP, L ∈ EXPPar A} ⊆ NPpoly ∩ coNPpoly := by sorry

end NKtLB.Supplement
