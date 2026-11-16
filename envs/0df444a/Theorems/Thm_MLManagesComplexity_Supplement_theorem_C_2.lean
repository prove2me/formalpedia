-- Prove2me | Theorems.Thm_MLManagesComplexity_Supplement_theorem_C_2
-- name    : MLManagesComplexity.Supplement.theorem_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:08:39.186824+00:00
-- url     : https://prove2.me/theorems/77a4d397-fb3f-4d09-88c9-f89a34dd6b29
-- title:
--   Theorem C.2 — next-bit pseudoentropy $k$ lower-bounds the log loss of every $C\in\mathcal P_{s,m}$ by $k-nm\epsilon$
-- statement:
--   There is a constant $c$ such that the following holds for all $n,s,m\in\mathbb N$, all reals $\epsilon,k$ and every distribution $D$ on $\{0,1\}^n$. If $D$ has $(s+c(m+n),\epsilon)$-next-bit pseudoentropy at least $k$, then every next-bit predictor $C\in\mathcal P_{s,m}$ satisfies
--
--   $$
--   \mathbb E_{x\sim D}\Big[\log\frac{1}{\mu_C(x)}\Big]\ \ge\ k-nm\epsilon .
--   $$
--
--   In other words, the efficient cross-entropy satisfies $\mathrm{CE}_{s,m}(D)\ge k-nm\epsilon$: no small next-bit predictor achieves log loss noticeably below the next-bit pseudoentropy of the data, so pseudoentropy lower-bounds the loss any efficient model can reach.
--
--   **Formalization Note** The constant $c$ is a natural number fixed before all other quantities. Next-bit predictors, $\mu_C$, $\mathcal P_{s,m}$ and next-bit pseudoentropy are the definitions `PredClass` and `HasNextBitPseudoentropy` of this supplement; circuits are the published Boolean circuits, logarithms are base 2.
--
--   Differences from the source:
--   - reading: a standard encoding of strings of length less than n (predictors); input an index i ∈ [n] and a string in {0,1}^i (distinguishers) → padEnc (n−1) y = y, 1, zeros (n bits) and padEnc n w = w, 1, zeros (n+1 bits), from which i = |w| is read; reason: the paper fixes no encoding; these are linear length and convertible into each other by O(n) gates, which the c(m+n) term covers
--   - encoding: circuits; deterministic distinguishers; A(…) = 1 → well-formed published PPADSIS.SubexpSIS.Circuit, size counting inputs and gates; A outputs the one-bit string [true]; reason: the base mission's circuit model; the paper uses deterministic distinguishers throughout
--   - encoding: there is a constant c → ∃ c : ℕ, quantified before n, s, m, ϵ, k, D, C; reason: pseudoentropy against larger circuits implies it against smaller ones, so a real c can be replaced by ⌈c⌉
--   - encoding: random variables Y_1, …, Y_n jointly distributed with X → a law J on pairs (X, Y) whose first marginal is D; reason: the same object
--   - encoding: E_i with i uniform in [n] → (1/n)·∑_i, which is 0 at n = 0; reason: only the undefined case n = 0 gets a value; there condition 1 forces k ≤ 0 and the conclusion holds
--   - encoding: In other words, CE_{s,m}(D) ≥ k − nmϵ → only the form: every C ∈ P_{s,m} satisfies E_{x∼D}[log 1/µ_C(x)] ≥ k − nmϵ; reason: CE_{s,m}(D) is the minimum of that quantity over the finite set P_{s,m}, so the restatement is the same claim
-- source:
--   Fortnow, How Does Machine Learning Manage Complexity?, arXiv:2604.07233 (version of 2026-10-31, sha256 4874d83f…), Theorem C.2, p.20 (PDF p.21)

import Mathlib
import Definitions.Def_MLManagesComplexity_Supplement_HasNextBitPseudoentropy

set_option autoImplicit false

open PPADSIS.SubexpSIS

namespace MLManagesComplexity.Supplement

/-- **Theorem C.2** (Fortnow, *How Does Machine Learning Manage Complexity?*, arXiv:2604.07233
(version of 2026-10-31, sha256 4874d83f…), §C.1, printed p.20, PDF p.21): there is a constant `c`
such that, if `D` on `{0,1}^n` has `(s + c(m + n), ϵ)`-next-bit pseudoentropy at least `k`, then
every `C ∈ P_{s,m}` satisfies `E_{x∼D}[log 1/µ_C(x)] ≥ k − nmϵ`.

**Formalization Note** `c` is a natural number chosen before everything else (`n, s, m, ϵ, k, D, C`).
The paper's restatement `CE_{s,m}(D) ≥ k − nmϵ` is the same claim for the minimum over `P_{s,m}`
and is not stated separately. Predictor and distinguisher input encodings are the fixed
`padEnc (n − 1)` and `padEnc n`; logarithms are base 2. -/
theorem theorem_C_2 :
    ∃ c : ℕ, ∀ (n s m : ℕ) (ε k : ℝ) (D : PMF (Fin n → Bool)),
      HasNextBitPseudoentropy D (s + c * (m + n)) ε k →
        ∀ C : Circuit, PredClass n s m C →
          k - (n : ℝ) * m * ε ≤ expectedLogLoss D m C := by sorry

end MLManagesComplexity.Supplement
