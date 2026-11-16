-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_7
-- name    : NKtLB.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:38:50.850776+00:00
-- url     : https://prove2.me/theorems/b470cf40-68f9-48d3-9210-76409cf26334
-- title:
--   Theorem 7 — MKtP $\notin\mathsf{NTIME}\cap\mathsf{coNTIME}[n^{\mathrm{poly}\log n}]$ or Gap-MrnKtP $\notin\mathsf{pr}\text{-}\mathsf{BPTIME}[n^{\mathrm{poly}\log n}]^{\|\mathsf{NP}}$
-- statement:
--   **A quick lower bound consequence.** At least one of the following holds:
--   $$
--   \mathrm{MKtP}\notin\mathsf{NTIME}[n^{\mathrm{poly}(\log n)}]\cap\mathsf{coNTIME}[n^{\mathrm{poly}(\log n)}],
--   $$
--   or, for every $c_1\in\mathbb N$,
--   $$
--   \text{Gap-MrnKtP}[\,n-(\log n)^{c_1},\ n-1\,]\notin\mathsf{pr}\text{-}\mathsf{BPTIME}[n^{\mathrm{poly}(\log n)}]^{\|\mathsf{NP}},
--   $$
--   where $\|\mathsf{NP}$ denotes non-adaptive access to an NP oracle. The statement is unconditional. It follows from Theorem 5 and Theorem 6 by considering whether symmetry of information holds for $rn\mathrm{Kt}$ with polylogarithmic error.
--
--   MKtP is the problem of deciding $\mathrm{Kt}(x)\le s$ on input $(x,1^s)$. Whether MKtP is in P is a long-standing open question.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - reading: $\mathsf C[T]$ with time $O(T)$ on an unspecified machine model → time $c\cdot T+c$ on the base `Machine`; reason: standard classes, not defined in the paper; same reading as the base `NTIME`
--   - reading: $\mathsf C[n^{\mathrm{poly}(\log n)}]$ / $\mathsf C[n^{\mathrm{polylog}(n)}]$ → $\bigcup_{c\in\mathbb N}\mathsf C[\lceil n^{(\log_2 n)^c}\rceil]$; reason: the standard meaning of the class
--   - reading: non-adaptive (parallel) oracle access $\|$ → one round of `AdaptRounds` on every input and random string; reason: the paper gives no formal definition; this is the semantic one
--   - reading: oracle class NP in $\mathsf C^{\mathsf{NP}}$ → union over oracles $A\in\mathsf{NP}$; reason: standard meaning of relativization to a class
--   - reading: $s_1(n)=n-\mathrm{poly}(\log n)$ in the second disjunct → for every $c_1\in\mathbb N$, $s_1(n)=n-(\log_2 n)^{c_1}$; reason: the strongest reading (a larger $c_1$ gives an easier problem); the proof via Lemma 95 works for every exponent
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 7, p.11

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_MKtP
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_Supplement_qpoly
import Definitions.Def_NKtLB_Supplement_GapMrnKtP
import Definitions.Def_NKtLB_Supplement_NP
import Definitions.Def_NKtLB_Supplement_PrBPTIMEPar

namespace NKtLB.Supplement

/-- **Theorem 7 (A Quick Lower Bound Consequence)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 7, p.11): "The following result
holds: `MKtP ∉ NTIME[n^{poly(log n)}] ∩ coNTIME[n^{poly(log n)}]` or `Gap-MrnKtP[s₁, s₂] ∉
pr-BPTIME[n^{poly(log n)}]^{∥NP}`, where `s₁(n) = n − poly(log n)` and `s₂(n) = n − 1`."

**Formalization Note.** For every valid universal machine `U`. The classes `C[n^{poly(log n)}]` are
`⋃_c C[n^{(log n)^c}]`; `pr-BPTIME[T]^{∥NP} = ⋃_{A ∈ NP} pr-BPTIME[T]^{∥A}` (non-adaptive queries). The
second disjunct is read for every exponent `c₁`: `s₁(n) = n − (log₂ n)^{c₁}` for every `c₁ ∈ ℕ` (the
reading the proof supports; it is the strongest reading, since a larger `c₁` gives an easier
problem). -/
theorem theorem_7 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    MKtP U ∉ {L | ∃ c : ℕ, L ∈ NTIME (qpoly c)} ∩ {L | ∃ c : ℕ, L ∈ coNTIME (qpoly c)} ∨
    ∀ c₁ : ℕ, GapMrnKtP U (fun n => n - Real.logb 2 n ^ c₁) (fun n => n - 1) ∉
      {P | ∃ c₂ : ℕ, ∃ A ∈ NP, P ∈ PrBPTIMEPar A (qpoly c₂)} := by sorry

end NKtLB.Supplement
