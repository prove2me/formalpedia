-- Prove2me | Theorems.Thm_IllCondRegMem_theorem_1
-- name    : IllCondRegMem.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:58:48.121994+00:00
-- url     : https://prove2.me/theorems/871edc19-202c-43cc-8728-0a8b5e860df8
-- title:
--   Theorem 1 — polynomial memory/sample tradeoff: against adaptive $d^{12}\log d$-conditioned covariates, recovery needs $\Omega(d^{2-\delta}\log d)$ bits or $d^{1+\delta}$ samples
-- statement:
--   Let a learner with $M$ memory bits and $T$ samples face non-i.i.d. linear regression in $\mathbb R^d$: the target is $x^\star\sim\mathcal N(0,I/d)$, and on each round an adaptive adversary selects a covariance matrix $\Sigma_t$ with condition number at most
--   $$
--   \kappa=d^{12}\log d
--   $$
--   and reveals $(a_t,a_t^\top x^\star)$ with $a_t\sim\mathcal N(0,\Sigma_t)$. Suppose that, against every such adversary, the learner recovers $x^\star$ to accuracy $\epsilon$ (i.e. $\|\hat x-x^\star\|\le\epsilon$) with probability at least $1/3$.
--
--   There are an absolute constant $c>0$ and a dimension $d_0$ such that for all $d\ge d_0$ and all $\delta\in[0,1]$:
--
--   1. (polynomial accuracy) if $\epsilon=1/\sqrt d$, then $M\ge c\,d^{2-\delta}\log d$ or $T\ge d^{1+\delta}$;
--   2. (constant accuracy) if $\epsilon=1/5$, then $M\ge c\,d^{2-\delta}$ or $T\ge d^{1+\delta}$.
--
--   Gaussian elimination solves the problem with $O(d^2\log d)$ bits and $O(d)$ samples, so any learner with polynomially less memory pays a polynomial factor $d^\delta$ in samples. This is the first beyond-logarithmic memory/sample separation for linear regression.
--
--   **Formalization Note** Learners, adversaries and success probabilities are those of the definitions `Learner`, `Adversary` and `succProb`.
--
--   Differences from the source:
--   - reading: Ω(d^{2−δ} log d) and Ω(d^{2−δ}) bits, for any fixed δ ∈ [0,1] → one absolute c > 0 and threshold d₀, chosen before δ, M, T and the learner; reason: the stronger reading: constants uniform in δ
--   - reading: log in κ = d¹² log d → natural logarithm; reason: the paper's bounds (56), (61) use ln; a base-2 log would enlarge the adversary class
--   - encoding: randomized branching program with M bits, Memory₀ = 0 → Learner: per-round uniform seeds, no shared seed, memory Fin M → Bool starting all-false, measurable maps; reason: every randomized update into a finite set is realized from a uniform seed; measurability makes the probability defined
--   - encoding: any adaptive adversary selecting κ-conditioned Σ_t, dependent on target, history and memory → Adversary: measurable map from (seed, x⋆, past samples, Memory_{t−1}) to a factor A_t with a_t = A_t g_t and A_tA_tᵀ κ-conditioned; reason: N(0, AAᵀ) is the law of Ag, so every covariance choice is available
--   - encoding: rounds t ≥ 1, T samples; accuracy ϵ with probability at least 1/3 → rounds 0, …, T−1; seedLaw-probability of ‖x̂ − x⋆‖ ≤ ε at least 1/3 for every adversary; reason: Lean indexing and event S_ϵ of p.36
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Theorem 1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_IllCondRegMem_succProb

open MeasureTheory ProbabilityTheory

namespace IllCondRegMem

/-- **Theorem 1 (Polynomial memory/sample-complexity tradeoff).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Theorem 1,
p.3: "Let alg be an algorithm such that for an unknown target x⋆ ∼ N(0, I/d), and any adaptive
adversary selecting κ = d¹² log d-conditioned covariance matrices Σ_t on each round t ≥ 1 then
revealing the regression sample (a_t, a_tᵀx⋆) for a_t ∼ N(0, Σ_t), the algorithm alg recovers x⋆
to accuracy ϵ with probability at least 1/3. Fix any δ ∈ [0, 1]. For polynomial accuracy
ϵ = 1/√d (resp. constant accuracy ϵ = 1/5), alg uses at least Ω(d^{2−δ} log d) bits of memory
(resp. Ω(d^{2−δ}) bits of memory), or requires at least d^{1+δ} samples."

**Formalization Note.** `Ω(·)` is read with one absolute constant `c > 0` and one dimension
threshold `d₀`, both chosen before `δ`, the memory `M`, the horizon `T` and the learner; the
sample threshold is `d^{1+δ}` exactly as printed. `κ = d¹² log d` uses the natural logarithm.
Learners, adversaries and the success probability are those of `Learner`, `Adversary` and
`succProb` (per-round fresh seeds, no shared learner seed; the adversary sees its seed, `x⋆`,
the past samples and the current memory). -/
theorem theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
      ∀ (M T : ℕ) (alg : Learner d M T),
        (SucceedsAgainstAll alg ((d : ℝ) ^ 12 * Real.log d) (1 / Real.sqrt d) →
            c * (d : ℝ) ^ (2 - δ) * Real.log d ≤ M ∨ (d : ℝ) ^ (1 + δ) ≤ T) ∧
        (SucceedsAgainstAll alg ((d : ℝ) ^ 12 * Real.log d) (1 / 5) →
            c * (d : ℝ) ^ (2 - δ) ≤ M ∨ (d : ℝ) ^ (1 + δ) ≤ T) := by sorry

end IllCondRegMem
