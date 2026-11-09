-- Prove2me | Theorems.Thm_NAMatchEst_lemma_3_14
-- name    : NAMatchEst.lemma_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:59:00.755013+00:00
-- url     : https://prove2.me/theorems/599d495e-172c-42c9-8b28-10673a1a0555
-- title:
--   Lemma 3.14 — cost of one truncated trial
-- statement:
--   Throughout, $n^{1/3}\le\alpha\le n^{1/2}$ is real and $k$ is an integer with $\alpha\le k\le n$ (the standing setup of §3.2, p.19); $C_0=2^{20}$, $c=10^5$ and $L=\ln(2n)$. Let $n$ be sufficiently large.
--
--   One truncated trial uses at most
--
--   $$
--   O\Big(L\cdot\begin{cases} n/\sqrt\alpha, & k\le\alpha^2,\\ n\sqrt k/\alpha^{3/2}, & k>\alpha^2\end{cases}\Big)
--   $$
--
--   queries on every outcome of its randomness. Every query is fixed before any oracle answer is received.
--
--   **Formalization Note** Non-adaptivity is the type of the trial (`RandAlg`); one constant for the $O(\cdot)$ and one threshold for "sufficiently large", both chosen before $n$, $\alpha$, $k$.
--
--   Differences from the source:
--   - reading: the standing assumption of §3.2 that n exceeds a sufficiently large universal constant (p.19) → ∃ N₀, ∀ n ≥ N₀, with N₀ chosen before n, α, k; reason: the source's standing assumption, made explicit
--   - reading: O(·) → one constant D chosen before n, α and k; reason: the uniform reading of a universal constant
--   - generalization: identical oracle queries may be answered once (p.20) → every occurrence of a query is charged; reason: a bound on the charged count implies the source's bound
--   - encoding: Bernoulli samples with probabilities p^L, p^R → product distribution bernDist with p clamped to [0,1]; reason: for n ≥ N₀ the source's assumption cL/√α ≤ 1 puts both probabilities in [0,1], where the clamp does nothing
-- source:
--   Khanna–Mukhopadhyay–Shah, Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.14, p.30 (PDF 34)

import Mathlib
import Definitions.Def_NAMatchEst_RandAlg
import Definitions.Def_NAMatchEst_RandAlg_CostLE
import Definitions.Def_NAMatchEst_L
import Definitions.Def_NAMatchEst_truncTrial

namespace NAMatchEst

/-- **Lemma 3.14 (Cost of one trial).** One truncated trial uses at most
`O(L · (n/√α if k ⩽ α², n√k/α^{3/2} if k > α²))` queries. Every query is fixed before receiving
any oracle answer.

Khanna–Mukhopadhyay–Shah, *Tight Non-Adaptive Query-Approximation Tradeoffs for Maximum Matching Size Estimation*, STOC 2027 submission (manuscript, sha256 0e4af57b…c9ad), Lemma 3.14, p.30 (PDF 34), in the standing setup of §3.2, p.19 (PDF 23), including "n
exceeds a sufficiently large universal constant" (used on p.29–30: "both npL and npR are at least
L for sufficiently large n").

**Formalization Note** One constant `D` and one threshold `N₀`, chosen before `n`, `α`, `k`; the
bound holds for every seed. Non-adaptivity ("Every query is fixed before receiving any oracle
answer") is built into the type `RandAlg` of `truncTrial`. -/
theorem lemma_3_14 : ∃ D : ℝ, ∃ N₀ : ℕ, ∀ (n : ℕ) [NeZero n], N₀ ≤ n → ∀ (α : ℝ) (k : ℕ),
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    (truncTrial n α k).CostLE (D * L n *
      (if (k : ℝ) ≤ α ^ 2 then n / Real.sqrt α else n * Real.sqrt k / α ^ ((3 : ℝ) / 2))) := by sorry

end NAMatchEst
