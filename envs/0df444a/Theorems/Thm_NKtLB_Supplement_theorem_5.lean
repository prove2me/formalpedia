-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_5
-- name    : NKtLB.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:38:01.611086+00:00
-- url     : https://prove2.me/theorems/3e62811d-1a37-427a-b088-c31326153edd
-- title:
--   Theorem 5 — SoI gives Gap-MrnKtP $\in\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly}$ and MKtP $\notin\mathsf{NTIME}\cap\mathsf{coNTIME}[n^{\mathrm{poly}\log n}]$
-- statement:
--   **Refined meta-complexity landscape under symmetry of information.**
--
--   1. *(Nonuniform upper bound.)* If SoI with error $O(\log n)$ holds for $rn\mathrm{Kt}$, then there is $d>0$ such that
--   $$
--   \text{Gap-MrnKtP}[\,n-d\log n,\ n-1\,]\in\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly}.
--   $$
--   2. *(Uniform lower bound.)* If SoI with error $\mathrm{poly}(\log n)$ holds for $n\mathrm{Kt}$ or for $rn\mathrm{Kt}$, then
--   $$
--   \mathrm{MKtP}\notin\mathsf{NTIME}[n^{\mathrm{poly}(\log n)}]\cap\mathsf{coNTIME}[n^{\mathrm{poly}(\log n)}].
--   $$
--
--   A promise problem lies in a class if some language of the class contains its YES instances and avoids its NO instances (p.10). Here $n\mathrm{Kt}$ is the nondeterministic Levin–Kolmogorov complexity of the base mission, $rn\mathrm{Kt}=rn\mathrm{Kt}_{2/3}$, $pn\mathrm{Kt}=pn\mathrm{Kt}_{2/3}$, and all measures are taken with respect to an arbitrary valid universal machine $U$.
--
--   Part 1 is implausible, since it would certify an approximation of $rn\mathrm{Kt}$ in $\mathsf{NP}/\mathsf{poly}\cap\mathsf{coNP}/\mathsf{poly}$. Part 2, combined with the correspondence of Theorem 6, yields the unconditional Theorem 7.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - encoding: $\mu(x,y)$ for an implicit pairing → $\mu$ of `tupleEnc [x, y]`; reason: the paper leaves the pairing implicit (p.22: robust to encoding choices)
--   - reading: SoI with error $e(n)=O(\log n)$ (p.5) → $\exists c>0\,\exists N\,\forall n\ge N$: SoI at length $n$ with error $c\log_2 n$; reason: an $O(\log n)$ bound constrains only large $n$; at $n\le1$ a literal $c\log n$ is $0$ and would demand exact additivity
--   - reading: SoI with error $e(n)=\mathrm{poly}(\log n)$ → $\exists c>0\,\exists N\,\forall n\ge N$: SoI at length $n$ with error $(\log_2 n)^c$; reason: standard meaning of $\mathrm{poly}(\log n)$, matching the explicit form of Theorems 59/65
--   - reading: $\mathsf C[T]$ with time $O(T)$ on an unspecified machine model → time $c\cdot T+c$ on the base `Machine`; reason: standard classes, not defined in the paper; same reading as the base `NTIME`
--   - reading: $\mathsf C[n^{\mathrm{poly}(\log n)}]$ / $\mathsf C[n^{\mathrm{polylog}(n)}]$ → $\bigcup_{c\in\mathbb N}\mathsf C[\lceil n^{(\log_2 n)^c}\rceil]$; reason: the standard meaning of the class
--   - reading: Gap-MrnKtP$[n-O(\log n),n-1]$ → $\exists d>0$, Gap-MrnKtP$[n-d\log_2 n,\,n-1]$; reason: the proof (Lemma 88, p.60) yields one constant $d$; a larger $d$ gives an easier problem
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 5, p.10

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_SoIAt
import Definitions.Def_NKtLB_Supplement_rnKt
import Definitions.Def_NKtLB_nKt
import Definitions.Def_NKtLB_Supplement_GapMrnKtP
import Definitions.Def_NKtLB_Supplement_PromiseIn
import Definitions.Def_NKtLB_Supplement_NPpoly
import Definitions.Def_NKtLB_Supplement_coNPpoly
import Definitions.Def_NKtLB_Supplement_MKtP
import Definitions.Def_NKtLB_NTIME
import Definitions.Def_NKtLB_coNTIME
import Definitions.Def_NKtLB_Supplement_qpoly

namespace NKtLB.Supplement

/-- **Theorem 5 (Refined Meta-Complexity Landscape Under SoI)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 5, p.10): "The
following results hold:
(i) [Nonuniform Upper Bound] If SoI with error `e(n) = O(log n)` holds for rnKt, then
`Gap-MrnKtP[n − O(log n), n − 1] ∈ NP/poly ∩ coNP/poly`.
(ii) [Uniform Lower Bound] If SoI with error `e(n) = poly(log n)` holds for either nKt or rnKt, then
`MKtP ∉ NTIME[n^{poly(log n)}] ∩ coNTIME[n^{poly(log n)}]`."

**Formalization Note.** For every valid universal machine `U` (base readings R1, R2). "SoI holds
for `μ` with error `e(n) = O(log n)`" is `∃ c > 0, ∃ N, ∀ n ≥ N, SoIAt μ n (c·log₂ n)` and "with error
`e(n) = poly(log n)`" is `∃ c > 0, ∃ N, ∀ n ≥ N, SoIAt μ n ((log₂ n)^c)` (p.5 definition; an `O(·)`
bound constrains only large `n`). `nKt` is the base `nKt` with `O = ∅`, `rnKt = rnKt_{2/3}` (p.22). In (i), `n − O(log n)` is `n − d·log₂ n` for some `d > 0` (the proof, via Lemma 88, p.60,
gives one such `d`), and promise membership is `PromiseIn` (p.10). In (ii),
`NTIME[n^{poly(log n)}] = ⋃_c NTIME[n^{(log n)^c}]`, likewise for coNTIME. -/
theorem theorem_5 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ((∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => rnKt U ∅ (2 / 3) x y) n (c * Real.logb 2 n)) →
      ∃ d : ℝ, 0 < d ∧ PromiseIn (GapMrnKtP U (fun n => n - d * Real.logb 2 n) (fun n => n - 1))
        (NPpoly ∩ coNPpoly)) ∧
    (((∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => nKt U ∅ ⊤ x y []) n (Real.logb 2 n ^ c)) ∨ (∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SoIAt (fun x y => rnKt U ∅ (2 / 3) x y) n (Real.logb 2 n ^ c))) →
      MKtP U ∉ {L | ∃ c : ℕ, L ∈ NTIME (qpoly c)} ∩ {L | ∃ c : ℕ, L ∈ coNTIME (qpoly c)}) := by sorry

end NKtLB.Supplement
