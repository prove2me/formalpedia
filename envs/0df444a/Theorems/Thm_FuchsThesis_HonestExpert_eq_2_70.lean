-- Prove2me | Theorems.Thm_FuchsThesis_HonestExpert_eq_2_70
-- name    : FuchsThesis.HonestExpert.eq_2_70
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:00.315631+00:00
-- url     : https://prove2.me/theorems/782d883f-121c-48f0-9d6e-9345bf60f4ef
-- title:
--   (2.70) — the Shannon inequality $\sum p_k\ln q_k\le\sum p_k\ln p_k$, with equality iff $p=q$
-- statement:
--   Let $p = (p_1, \dots, p_n)$ and $q = (q_1, \dots, q_n)$ be probability distributions ($p_k, q_k \ge 0$, $\sum_k p_k = \sum_k q_k = 1$) such that $q_k > 0$ whenever $p_k > 0$. Then
--
--   $$\sum_{k=1}^{n} p_k \ln q_k \;\le\; \sum_{k=1}^{n} p_k \ln p_k ,$$
--
--   with equality if and only if $p_k = q_k$ for all $k$. Terms with $p_k = 0$ are read as $0$ on both sides (the convention $0 \ln 0 = 0$).
--
--   This is the "if" half of Theorem 2.3: with $F_k(p) = \alpha \ln p + \gamma_k$ and $\alpha \ge 0$, the expected payoff of a report $q$ falls short of that of the truth $p$ by $\alpha$ times the Kullback–Leibler information $\sum_k p_k \ln(p_k/q_k) \ge 0$, which vanishes only for an honest report.
--
--   **Formalization Note** $\ln$ is `Real.log`, with Lean's $\ln 0 = 0$; a term $p_k \ln(\cdot)$ with $p_k = 0$ is $0$.
--
--   Differences from the source:
--   - generalization: strictly positive n-point distributions p, q → p, q nonnegative probability distributions with q_k > 0 whenever p_k > 0; reason: the hypothesis is weaker and contains the strictly positive case used by Theorem 2.3
--   - encoding: 0 ln 0 → Real.log 0 = 0, so 0 · ln 0 = 0; reason: Lean convention, the usual convention for entropy-type sums; no strictly positive instance is affected
--   - encoding: outcomes 1, …, n → Fin n; reason: Lean indexing
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.3.1, eq. (2.70), p.24 (PDF p.33)

import Mathlib

namespace FuchsThesis.HonestExpert

/-- **(2.70): the Shannon inequality, with its equality case.**
Fuchs, *Distinguishability and Accessible Information in Quantum Theory*, arXiv:quant-ph/9601020v1,
§2.3.1, eq. (2.70), p.24 (PDF p.33): "the Shannon inequality,
∑_{k=1}^n p_k ln q_k ≤ ∑_{k=1}^n p_k ln p_k, with equality if and only if p_k = q_k for all k."

Let `p, q : Fin n → ℝ` be probability distributions (nonnegative entries summing to one) such that
`q_k > 0` whenever `p_k > 0`. Then `∑_k p_k ln q_k ≤ ∑_k p_k ln p_k`, with equality if and only if
`p = q`.

**Formalization Note.** `ln` is `Real.log`, with Lean's `Real.log 0 = 0`; every term with `p_k = 0`
is `0 · ln(·) = 0` on both sides, the usual convention `0 ln 0 = 0`. The page proves (2.70) for the
strictly positive distributions of Theorem 2.3; the statement here allows zeros in `p` (and in `q`
where `p` vanishes), which contains that case. -/
theorem eq_2_70 {n : ℕ} (p q : Fin n → ℝ) (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1) (hpq : ∀ k, 0 < p k → 0 < q k) :
    ∑ k, p k * Real.log (q k) ≤ ∑ k, p k * Real.log (p k) ∧
      (∑ k, p k * Real.log (q k) = ∑ k, p k * Real.log (p k) ↔ p = q) := by sorry

end FuchsThesis.HonestExpert
