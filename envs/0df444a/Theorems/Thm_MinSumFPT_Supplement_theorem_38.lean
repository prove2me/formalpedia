-- Prove2me | Theorems.Thm_MinSumFPT_Supplement_theorem_38
-- name    : MinSumFPT.Supplement.theorem_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:18:28.98116+00:00
-- url     : https://prove2.me/theorems/b4998202-03dc-4e1d-830c-c1b99bb0cc01
-- title:
--   Theorem 38 — assuming OVH, gap 2-maxcoverage over a universe of size $c\log n$ needs time $n^{2-\varepsilon}$
-- statement:
--   Assume the Orthogonal Vectors Hypothesis. Then for every $\varepsilon>0$ there exist $\delta=\delta(\varepsilon)>0$ and $c=c(\varepsilon)>0$ such that no algorithm running in time $O(n^{2-\varepsilon})$ can distinguish, for $n$ sets $S_1,\dots,S_n$ over a universe $U$ with $1\le|U|\le c\log_2 n$, between
--
--   1. **completeness**: some $i,j\in[n]$ and an equipartition $U=U_1\sqcup U_2$ have $U_1\subseteq S_i$ and $U_2\subseteq S_j$;
--   2. **soundness**: for every $i,j\in[n]$,
--   $$
--   |S_i\cup S_j|\le(1-\delta)\,|U|.
--   $$
--
--   Precisely: there are no admissible program and constants $K,n_0$ such that for all $n\ge n_0$, on every such instance, the program outputs $1$ in the completeness case and $0$ in the soundness case, on every random tape, within $K\,n^{2-\varepsilon}$ steps.
--
--   This is the maxcoverage problem with an optimum of two sets, the intermediate problem from which Theorem 39 derives the subquadratic lower bound for balanced 2-median.
--
--   **Formalization Note** Algorithms are admissible programs of `MinSumFPT.Machine` run on the integer encoding of the set system (`MinSumFPT.Supplement.InputMachine`), as in OVH.
--
--   Differences from the source:
--   - generalization: OVH: A, B ⊆ {0,1}^d sets, d = C log n, no O(n^{2−ϵ})-time algorithm → OVH over lists of n vectors (repeats allowed), d = ⌈C·log₂ n⌉, no program answering every instance with n ≥ 1 within K·n^{2−ϵ}; reason: a weaker hypothesis implied by the page's: sets are lists without repeats, a program for dimension ⌈C log₂ n⌉ ≥ C log n solves the smaller dimension by zero padding, and finitely many instances of each size make a threshold n₀ irrelevant
--   - reading: an algorithm (no machine named) → an admissible program of MinSumFPT.Machine run on the explicit input (MinSumFPT.Supplement.inputState), answering on every random tape; reason: the page names no machine; the published machine of the mission, with the same instruction set as Theorem 1; the guarantee on every tape is the deterministic reading of 'algorithm', the same reading as in OVH, so the reduction of the proof stays in one model
--   - reading: no n^{2−ε}-time algorithm → no program with constants K, n₀ answering within K·n^{2−ε} steps for all n ≥ n₀; reason: at least as strong as the literal 'time ≤ n^{2−ε}'; OVH forbids O(n^{2−ϵ}) and the proof's reduction adds O(n log n)
--   - reading: can distinguish between the two cases → output 1 on every completeness instance and 0 on every soundness instance; nothing is required on other instances; reason: a promise problem, as on the page
--   - reading: a universe U of size c·log n → 1 ≤ |U| ≤ c·log₂ n with c = c(ε) > 0; reason: the proof's universe has size ℓ·2^{D̃} with ℓ ≤ c·log n, at most a constant multiple of log n; the base of the logarithm is absorbed in c; on the empty universe both cases hold at once
--   - encoding: sets S_1, …, S_n over U, an equipartition U = U_1 ∪̇ U_2 → S : Fin n → Finset (Fin m), U₁ and its complement with |U₁| = |U₁ᶜ|; input [n, m, membership bits]; reason: same instances; 0-based indices
-- source:
--   Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 38, p.45 (PDF p.46); Hypothesis 2 (OVH), p.43

import Mathlib
import Definitions.Def_MinSumFPT_Machine
import Definitions.Def_MinSumFPT_Supplement_InputMachine
import Definitions.Def_MinSumFPT_Supplement_OVH
import Definitions.Def_MinSumFPT_Supplement_MaxCov2
set_option autoImplicit false

namespace MinSumFPT.Supplement

/-- Theorem 38 (Karthik C. S.–Lee–Rabani–Schwiegelshohn–Zhou, *A Fixed Parameter Sublinear Time Approximation Scheme for Metric Min-Sum Clustering*, arXiv:2610.15148 (held version of November 2, 2026, sha256 12e81235…), Theorem 38, p.45): assuming OVH, for every `ε > 0` there exist
`δ = δ(ε) > 0` and `c = c(ε)` such that no `n^{2−ε}`-time algorithm that takes as input sets
`S_1, …, S_n` over a universe `U` of size `c · log n` can distinguish the completeness case (two
sets cover the two halves of an equipartition of `U`) from the soundness case (every two sets cover
at most `(1 − δ)|U|`).

**Formalization Note.** Algorithms are admissible programs of `MinSumFPT.Machine` run on the
explicit input `encodeSets S` (`MinSumFPT.Supplement.inputState`), correct on every tape.
"No `n^{2−ε}`-time algorithm" is read as: no program and constants `K, n₀` such that for all
`n ≥ n₀` and all instances with `1 ≤ |U| ≤ c · log₂ n` the program answers YES (output `1`) on
completeness instances and NO (output `0`) on soundness instances within `K · n^{2−ε}` steps.
Nothing is required on other instances (a promise problem). The universe is nonempty: on the
empty universe both cases hold at once. -/
theorem theorem_38 (hOVH : OVH) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ c : ℝ, 0 < c ∧
      ¬ ∃ P : Program, Admissible P ∧ ∃ (K : ℝ) (n₀ : ℕ), ∀ n m : ℕ, n₀ ≤ n → 1 ≤ m →
        (m : ℝ) ≤ c * Real.logb 2 n → ∀ S : Fin n → Finset (Fin m),
          (MaxCovYes S → AnswersWithin P (encodeSets S) [] true (K * (n : ℝ) ^ (2 - ε))) ∧
          (MaxCovNo δ S → AnswersWithin P (encodeSets S) [] false (K * (n : ℝ) ^ (2 - ε))) := by sorry

end MinSumFPT.Supplement
