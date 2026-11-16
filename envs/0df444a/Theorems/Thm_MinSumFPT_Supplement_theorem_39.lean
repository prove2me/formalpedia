-- Prove2me | Theorems.Thm_MinSumFPT_Supplement_theorem_39
-- name    : MinSumFPT.Supplement.theorem_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:19:01.908275+00:00
-- url     : https://prove2.me/theorems/01c89f83-c263-471c-8345-1d7cd5e43137
-- title:
--   Theorem 39 — assuming OVH, balanced 2-median with $O_\varepsilon(\log n)$ clients needs time $n^{2-\varepsilon}$
-- statement:
--   Assume the Orthogonal Vectors Hypothesis. Then for every $\varepsilon>0$ there exist $\delta=\delta(\varepsilon)>0$ and $c=c(\varepsilon)>0$ such that no algorithm running in time $O(n^{2-\varepsilon})$ can distinguish, for facilities $f_1,\dots,f_n$, clients $c_1,\dots,c_m$ with $1\le m\le c\log_2 n$ and a distance function $\Delta:C\times F\to\mathbb R_{\ge0}$, between
--
--   1. **completeness**: some $i,j\in[n]$ and an equipartition $C=C_1\sqcup C_2$ have
--   $$
--   \sum_{c\in C_1}\Delta(c,f_i)+\sum_{c\in C_2}\Delta(c,f_j)=|C|;
--   $$
--   2. **soundness**: for every $i,j\in[n]$,
--   $$
--   \sum_{c\in C}\min\{\Delta(c,f_i),\Delta(c,f_j)\}\ge(1+\delta)\,|C|.
--   $$
--
--   Precisely: there are no admissible program and constants $K,n_0$ such that for all $n\ge n_0$, on every such instance, the program outputs $1$ in the completeness case and $0$ in the soundness case, on every random tape, within $K\,n^{2-\varepsilon}$ steps.
--
--   This is the formal version of Theorem 2: under OVH neither balanced 2-median nor 2-median admits a subquadratic approximation scheme, in contrast with the near-linear time scheme of Theorem 1 for k-minsum clustering.
--
--   **Formalization Note** Algorithms are admissible programs of `MinSumFPT.Machine` run on $[n,m]$ and the distances in real memory (`MinSumFPT.Supplement.InputMachine`), as in OVH.
--
--   Differences from the source:
--   - generalization: OVH: A, B ⊆ {0,1}^d sets, d = C log n, no O(n^{2−ϵ})-time algorithm → OVH over lists of n vectors (repeats allowed), d = ⌈C·log₂ n⌉, no program answering every instance with n ≥ 1 within K·n^{2−ϵ}; reason: a weaker hypothesis implied by the page's: sets are lists without repeats, a program for dimension ⌈C log₂ n⌉ ≥ C log n solves the smaller dimension by zero padding, and finitely many instances of each size make a threshold n₀ irrelevant
--   - reading: an algorithm (no machine named) → an admissible program of MinSumFPT.Machine run on the explicit input (MinSumFPT.Supplement.inputState), answering on every random tape; reason: the page names no machine; the published machine of the mission, with the same instruction set as Theorem 1; the guarantee on every tape is the deterministic reading of 'algorithm', the same reading as in OVH, so the reduction of the proof stays in one model
--   - reading: no n^{2−ε}-time algorithm → no program with constants K, n₀ answering within K·n^{2−ε} steps for all n ≥ n₀; reason: at least as strong as the literal 'time ≤ n^{2−ε}'; OVH forbids O(n^{2−ϵ}) and the proof's reduction adds O(n log n)
--   - reading: can distinguish between the two cases → output 1 on every completeness instance and 0 on every soundness instance; nothing is required on other instances; reason: a promise problem, as on the page
--   - reading: m = O_ε(log n) clients → 1 ≤ m ≤ c·log₂ n with c = c(ε) > 0; reason: O_ε(log n) is a bound c(ε)·log n; the base is absorbed in c; with no client both cases hold at once
--   - encoding: ∆ : C × F → ℝ≥0, an equipartition C = C_1 ∪̇ C_2 → Δ : Fin m → Fin n → ℝ with 0 ≤ Δ, C₁ and its complement with |C₁| = |C₁ᶜ|; input [n, m] and the distances in real memory; reason: same instances; the distances are real data, one unit per read
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 39, p.47 (PDF p.48), the formal version of Theorem 2, p.2; Hypothesis 2 (OVH), p.43

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumFPT_Supplement_InputMachine
import Definitions.Def_MinSumFPT_Supplement_OVH
import Definitions.Def_MinSumFPT_Supplement_Median2
set_option autoImplicit false

namespace MinSumFPT.Supplement

/-- Theorem 39 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 39, p.47; the formal version of Theorem 2, p.2): assuming OVH, for
every `ε > 0` there exists `δ = δ(ε) > 0` such that no `n^{2−ε}`-time algorithm that takes as input
facilities `f_1, …, f_n`, clients `c_1, …, c_m` (`m = O_ε(log n)`) and a distance function
`∆ : C × F → ℝ≥0` can distinguish the completeness case (an equipartition `C = C_1 ∪̇ C_2` and
`i, j` with `∑_{C_1} ∆(c, f_i) + ∑_{C_2} ∆(c, f_j) = |C|`) from the soundness case (for every
`i, j`, `∑_C min{∆(c, f_i), ∆(c, f_j)} ≥ (1 + δ)|C|`).

**Formalization Note.** Algorithms are admissible programs of `MinSumFPT.Machine` run on the
explicit input `encodeMedian ∆` (integers `n, m`; the distances in real memory), correct on every
tape. `m = O_ε(log n)` is read as `1 ≤ m ≤ c · log₂ n` for a constant `c = c(ε) > 0`; "no
`n^{2−ε}`-time algorithm" as: no program and constants `K, n₀` that, for all `n ≥ n₀`, answer YES
(output `1`) on every completeness instance and NO (output `0`) on every soundness instance within
`K · n^{2−ε}` steps (a promise problem). At least one client is required: with none both cases
hold. -/
theorem theorem_39 (hOVH : OVH) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧
      ¬ ∃ P : Program, Admissible P ∧ ∃ (K : ℝ) (n₀ : ℕ), ∀ n m : ℕ, n₀ ≤ n → 1 ≤ m →
        (m : ℝ) ≤ c * Real.logb 2 n → ∀ Δ : Fin m → Fin n → ℝ, (∀ u i, 0 ≤ Δ u i) →
          (MedianYes Δ → AnswersWithin P (encodeMedian Δ).1 (encodeMedian Δ).2 true
              (K * (n : ℝ) ^ (2 - ε))) ∧
          (MedianNo δ Δ → AnswersWithin P (encodeMedian Δ).1 (encodeMedian Δ).2 false
              (K * (n : ℝ) ^ (2 - ε))) := by sorry

end MinSumFPT.Supplement
