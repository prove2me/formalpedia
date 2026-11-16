-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_82
-- name    : NKtLB.Supplement.theorem_82
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:46:09.391696+00:00
-- url     : https://prove2.me/theorems/649d467d-5eb1-4e5c-997a-24b59fcd3d5f
-- title:
--   Theorem 82 — SoI for $rn\mathrm{Kt}$ implies $\mathsf{BPEXP}^{\|\mathsf{NP}}\subseteq\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly}$
-- statement:
--   Assume $rn\mathrm{Kt}$ satisfies symmetry of information with logarithmic error: there is $c>0$ such that for all strings $x,y$ (of any lengths)
--   $$
--   rn\mathrm{Kt}(x,y)\ \ge\ rn\mathrm{Kt}(x)+rn\mathrm{Kt}(y\mid x)-c\log(|x|+|y|).\qquad(16)
--   $$
--   Then
--   $$
--   \mathsf{BPEXP}^{\|\mathsf{NP}}\subseteq\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly},
--   $$
--   where $\|\mathsf{NP}$ denotes non-adaptive access to an NP oracle.
--
--   Here $n\mathrm{Kt}$ is the nondeterministic Levin–Kolmogorov complexity of the base mission, $rn\mathrm{Kt}=rn\mathrm{Kt}_{2/3}$, $pn\mathrm{Kt}=pn\mathrm{Kt}_{2/3}$, and all measures are taken with respect to an arbitrary valid universal machine $U$. Unlike Theorem 4(ii), the hypothesis (16) covers strings $x,y$ of different lengths, with error measured in $|x|+|y|$.
--
--   **Formalization Note** Lean requires (16) only for $|x|+|y|\ge N$, for some $N$.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: $\mathsf C[T]$ with time $O(T)$ on an unspecified machine model → time $c\cdot T+c$ on the base `Machine`; reason: standard classes, not defined in the paper; same reading as the base `NTIME`
--   - reading: non-adaptive (parallel) oracle access $\|$ → one round of `AdaptRounds` on every input and random string; reason: the paper gives no formal definition; this is the semantic one
--   - reading: oracle class NP in $\mathsf C^{\mathsf{NP}}$ → union over oracles $A\in\mathsf{NP}$; reason: standard meaning of relativization to a class
--   - generalization: Eq. (16) for all strings $x,y$ → Eq. (16) for all $x,y$ with $|x|+|y|\ge N$, for some $N$; reason: a weaker hypothesis: the printed one is the case $N=0$; at $|x|+|y|\le1$ the printed error $c\log(|x|+|y|)$ is $0$ or undefined and 'logarithmic error' does not intend exact additivity there
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 82, p.53, Eq. (16)

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_rnKt
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_NKtLB_Supplement_NP
import Definitions.Def_NKtLB_Supplement_BPEXPPar
import Definitions.Def_NKtLB_Supplement_NPpoly
import Definitions.Def_NKtLB_Supplement_coNPpoly

namespace NKtLB.Supplement

/-- **Theorem 82 (SoI for rnKt ⇒ `BPEXP^{∥NP} ⊆ NP/poly ∩ coNP/poly`)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 82, p.53):
"Assume that rnKt satisfies symmetry of information with logarithmic error, i.e., there exists a
constant `c > 0` such that for all strings `x, y`,
`rnKt(x, y) ≥ rnKt(x) + rnKt(y | x) − c log(|x| + |y|)`. (16)
Then `BPEXP^{∥NP} ⊆ NP/poly ∩ coNP/poly`."

**Formalization Note.** For every valid universal machine `U`. The hypothesis is ((16)) for all
strings `x, y` of any lengths with `|x| + |y| ≥ N` for some `N`: for `|x| + |y| ≤ 1` the printed error
`c log(|x| + |y|)` is `0` or undefined and ((16)) would demand exact additivity on the empty and
one-bit strings, which "logarithmic error" does not intend; the printed hypothesis is the case
`N = 0`. `rnKt` is `rnKt_{2/3}`;
`BPEXP^{∥NP} = ⋃_{A ∈ NP} BPEXP^{∥A}` (non-adaptive queries). -/
theorem theorem_82 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ x y : List Bool, N ≤ x.length + y.length →
      toEReal (rnKt U ∅ (2 / 3) x []) + toEReal (rnKt U ∅ (2 / 3) y x)
          - ((c * Real.logb 2 (x.length + y.length) : ℝ) : EReal)
        ≤ toEReal (rnKt U ∅ (2 / 3) (tupleEnc [x, y]) [])) →
      {L | ∃ A ∈ NP, L ∈ BPEXPPar A} ⊆ NPpoly ∩ coNPpoly := by sorry

end NKtLB.Supplement
