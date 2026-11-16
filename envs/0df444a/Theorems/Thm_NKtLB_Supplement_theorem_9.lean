-- Prove2me | Theorems.Thm_NKtLB_Supplement_theorem_9
-- name    : NKtLB.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:39:39.379368+00:00
-- url     : https://prove2.me/theorems/fd7d1639-920f-4683-a589-08fe01e9b520
-- title:
--   Theorem 9 — lower bounds for estimating rnKt against $\mathsf{AMTIME}$, $\mathsf{coAMTIME}$ and $\mathsf{SIZE}^O$
-- statement:
--   **Complexity lower bounds for estimating $rn\mathrm{Kt}$.**
--
--   1. For every $1/2<\gamma<1$ there is $\varepsilon>0$ with
--   $$
--   \text{Gap-MrnKtP}[\gamma n,\,n-1]\notin\mathsf{AMTIME}[2^{\varepsilon n}]\cap\mathsf{coAMTIME}[2^{\varepsilon n}].
--   $$
--   Moreover, for every $1/2<\gamma<1$ there is $\varepsilon(\gamma)>0$ such that no dense language $L\subseteq R_{rn\mathrm{Kt}}[\gamma n]$ is in $\mathsf{AMTIME}[2^{\varepsilon n}]\cap\mathsf{coAMTIME}[2^{\varepsilon n}]$.
--   2. For every $\gamma>0$, $\text{Gap-MrnKtP}[2^{\log^\gamma n},\,n-1]\notin\mathsf{AMTIME}[n^{\mathrm{polylog}(n)}]$. Moreover, no dense language $L\subseteq R_{rn\mathrm{Kt}}[2^{\log^\gamma n}]$ is in $\mathsf{coAMTIME}[n^{\mathrm{polylog}(n)}]$.
--   3. For every $\gamma>0$ and every $O\in\mathsf{AM}\cap\mathsf{coAM}$, $\text{Gap-MrnKtP}[2^{\log^\gamma n},\,n-1]\notin\mathsf{SIZE}^O[n^{\mathrm{polylog}(n)}]$. Moreover, no dense language $L\subseteq R_{rn\mathrm{Kt}}[2^{\log^\gamma n}]$ is in $\mathsf{SIZE}^O[n^{\mathrm{polylog}(n)}]$.
--
--   A language is **dense** if $|L\cap\{0,1\}^n|\ge 2^n/n^b$ for some $b>0$ and all large $n$ (p.12). A promise problem is not in a class if no language of the class separates its YES and NO instances. Here $n\mathrm{Kt}$ is the nondeterministic Levin–Kolmogorov complexity of the base mission, $rn\mathrm{Kt}=rn\mathrm{Kt}_{2/3}$, $pn\mathrm{Kt}=pn\mathrm{Kt}_{2/3}$, and all measures are taken with respect to an arbitrary valid universal machine $U$.
--
--   To the authors' knowledge these are the first lower bounds against $\mathsf{AM}$, $\mathsf{SIZE}[\mathrm{poly}]$ and exponential nondeterministic time for a natural meta-computational problem.
--
--   Differences from the source:
--   - generalization: a fixed time-efficient universal machine $U$ (p.22) → every pair (U, code) with `IsValidUniversal U code`; reason: the paper's fixed $U$ is one such pair, and the results are claimed for any such $U$ (p.22: robust to encoding choices)
--   - reading: $U$ simulates a machine in time $\tilde O(|M|,t)$ (p.21) → overhead $c_M\,t(\lceil\log t\rceil+1)+c_M$ with queries passed through (base `Simulates`); reason: the base mission's reading of the simulation condition, inherited
--   - encoding: complexities with $\min\emptyset=\infty$ → values in `ℕ∞` compared in `EReal` via `toEReal`; reason: Lean convention; same instances
--   - reading: $\mathsf C[T]$ with time $O(T)$ on an unspecified machine model → time $c\cdot T+c$ on the base `Machine`; reason: standard classes, not defined in the paper; same reading as the base `NTIME`
--   - reading: $\mathsf C[n^{\mathrm{poly}(\log n)}]$ / $\mathsf C[n^{\mathrm{polylog}(n)}]$ → $\bigcup_{c\in\mathbb N}\mathsf C[\lceil n^{(\log_2 n)^c}\rceil]$; reason: the standard meaning of the class
--   - reading: Boolean circuits with oracle access to $O$ of size $s(n)$ → straight-line circuits with oracle gates, size = number of gates; reason: the paper fixes no circuit model; polynomially related conventions give the same union over polylog exponents
--   - encoding: integer thresholds $s_1,s_2:\mathbb N\to\mathbb N$ (p.12) → real thresholds ($\gamma n$, $2^{(\log_2 n)^\gamma}$, $n-1$); reason: the theorem uses non-integer thresholds such as $\gamma n$; no rounding is introduced
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorem 9, pp.12–13

import Mathlib
import Definitions.Def_NKtLB_IsValidUniversal
import Definitions.Def_NKtLB_Supplement_GapMrnKtP
import Definitions.Def_NKtLB_Supplement_RrnKt
import Definitions.Def_NKtLB_Dense
import Definitions.Def_NKtLB_Supplement_PromiseIn
import Definitions.Def_NKtLB_Supplement_AMTIME
import Definitions.Def_NKtLB_Supplement_coAMTIME
import Definitions.Def_NKtLB_Supplement_AM
import Definitions.Def_NKtLB_Supplement_coAM
import Definitions.Def_NKtLB_Supplement_SIZEO
import Definitions.Def_NKtLB_Supplement_qpoly
import Definitions.Def_NKtLB_expBound

namespace NKtLB.Supplement

/-- **Theorem 9 (Complexity Lower Bounds for Estimating rnKt)** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorem 9, pp.12–13): "The
following statements hold:
1. For every constant `1/2 < γ < 1`, there exists a constant `ε > 0` such that
`Gap-MrnKtP[γ · n, n − 1] ∉ AMTIME[2^{εn}] ∩ coAMTIME[2^{εn}]`. Moreover, given a constant
`1/2 < γ < 1`, there exists `ε(γ) > 0` such that, for every dense language `L ⊆ R_{rnKt}[γ·n]`, we have
`L ∉ AMTIME[2^{εn}] ∩ coAMTIME[2^{εn}]`.
2. For every constant `γ > 0`, `Gap-MrnKtP[2^{log^γ n}, n − 1] ∉ AMTIME[n^{polylog(n)}]`. Moreover, for
every dense language `L ⊆ R_{rnKt}[2^{log^γ n}]`, we have `L ∉ coAMTIME[n^{polylog(n)}]`.
3. For every constant `γ > 0` and `O ∈ AM ∩ coAM`, `Gap-MrnKtP[2^{log^γ n}, n − 1] ∉
SIZE^O[n^{polylog(n)}]`. Moreover, for every dense language `L ⊆ R_{rnKt}[2^{log^γ n}]`, we have
`L ∉ SIZE^O[n^{polylog(n)}]`."

**Formalization Note.** For every valid universal machine `U`. A promise problem `∉ C` is
`¬ PromiseIn` (p.12); `2^{εn}` is the base `expBound ε`; `C[n^{polylog(n)}] = ⋃_c C[n^{(log n)^c}]`;
`log^γ n = (log₂ n)^γ`; dense is the base `Dense` (p.12). In items 2 and 3 the "moreover" part is
under the same `γ` (and `O`). -/
theorem theorem_9 (U : Machine) (code : Machine → List Bool) (hU : IsValidUniversal U code) :
    ((∀ γ : ℝ, 1 / 2 < γ → γ < 1 → ∃ ε : ℝ, 0 < ε ∧
        ¬ PromiseIn (GapMrnKtP U (fun n => γ * n) (fun n => n - 1))
          (AMTIME (expBound ε) ∩ coAMTIME (expBound ε))) ∧
      (∀ γ : ℝ, 1 / 2 < γ → γ < 1 → ∃ ε : ℝ, 0 < ε ∧ ∀ L : Set (List Bool), Dense L →
        L ⊆ RrnKt U (fun n => γ * n) → L ∉ AMTIME (expBound ε) ∩ coAMTIME (expBound ε))) ∧
    (∀ γ : ℝ, 0 < γ →
      ¬ PromiseIn (GapMrnKtP U (fun n => (2 : ℝ) ^ (Real.logb 2 n ^ γ)) (fun n => n - 1))
          {L | ∃ c : ℕ, L ∈ AMTIME (qpoly c)} ∧
      ∀ L : Set (List Bool), Dense L → L ⊆ RrnKt U (fun n => (2 : ℝ) ^ (Real.logb 2 n ^ γ)) →
        L ∉ {L' | ∃ c : ℕ, L' ∈ coAMTIME (qpoly c)}) ∧
    (∀ γ : ℝ, 0 < γ → ∀ O : Set (List Bool), O ∈ AM ∩ coAM →
      ¬ PromiseIn (GapMrnKtP U (fun n => (2 : ℝ) ^ (Real.logb 2 n ^ γ)) (fun n => n - 1))
          {L | ∃ c : ℕ, L ∈ SIZEO O (qpoly c)} ∧
      ∀ L : Set (List Bool), Dense L → L ⊆ RrnKt U (fun n => (2 : ℝ) ^ (Real.logb 2 n ^ γ)) →
        L ∉ {L' | ∃ c : ℕ, L' ∈ SIZEO O (qpoly c)}) := by sorry

end NKtLB.Supplement
