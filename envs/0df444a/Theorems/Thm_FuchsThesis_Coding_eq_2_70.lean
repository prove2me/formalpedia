-- Prove2me | Theorems.Thm_FuchsThesis_Coding_eq_2_70
-- name    : FuchsThesis.Coding.eq_2_70
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:20:57.816992+00:00
-- url     : https://prove2.me/theorems/1f80b25a-814b-4362-b986-61c025b97819
-- title:
--   Eq. (2.70) — Shannon inequality $\sum_k p_k\ln q_k \le \sum_k p_k \ln p_k$, with equality iff $p = q$
-- statement:
--   Let $p = (p_1,\dots,p_n)$ and $q = (q_1,\dots,q_n)$ be probability distributions, with $q_k > 0$ whenever $p_k > 0$. Then
--
--   $$
--   \sum_{k=1}^{n} p_k \ln q_k \;\le\; \sum_{k=1}^{n} p_k \ln p_k ,
--   $$
--
--   with equality if and only if $p_k = q_k$ for all $k$. Here $0 \ln 0 = 0$.
--
--   This is the Shannon (or Gibbs) inequality, the nonnegativity of the Kullback–Leibler information with its equality case. In the proof of Theorem 2.8 it is applied to $q(x_i) = 2^{-l(x_i)}/\sum_j 2^{-l(x_j)}$ to show that every instantaneous code has expected length at least $H(p)$.
--
--   Differences from the source:
--   - encoding: $\ln q_k$ for $n$-point distributions → the hypothesis $q_k > 0$ wherever $p_k > 0$; reason: it excludes exactly the terms $p_k \ln q_k$ with $p_k > 0 = q_k$, where $\ln q_k$ is not a real number, a nondegeneracy condition met by every pair of positive distributions and by the pair used in (2.138).
--   - encoding: terms with $p_k = 0$ → $0 \ln 0 = 0$ and $0 \ln q_k = 0$ (Mathlib's $\ln 0 = 0$); reason: the source's convention $0 \ln 0 = 0$ (p.32); no instance changes.
--   - encoding: points $k = 1,\dots,n$ → an arbitrary finite type; reason: Lean convention, same instances up to relabelling.
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (2.70), p.24 (PDF p.33); invoked in the proof of Theorem 2.8, p.39 (PDF p.48)

import Mathlib

namespace FuchsThesis.Coding

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (2.70), p.24 (PDF p.33), the Shannon inequality as invoked in the
proof of Theorem 2.8 (p.39): for probability distributions `p`, `q` on `n` points,
`∑ₖ pₖ ln qₖ ≤ ∑ₖ pₖ ln pₖ`, "with equality if and only if `pₖ = qₖ` for all `k`".

**Formalization Note.** Points form an arbitrary finite type. Zero entries are allowed, with the
convention `0 ln 0 = 0` (`Real.log 0 = 0` in Mathlib). The hypothesis `hsupp` (`qₖ > 0` wherever
`pₖ > 0`) excludes exactly the terms `pₖ ln qₖ` with `pₖ > 0 = qₖ`, where `ln qₖ` is not a real
number; every pair of strictly positive distributions satisfies it, and so does the pair `(p, q)` of
(2.138)–(2.139), where `q > 0` everywhere. -/
theorem eq_2_70 {ι : Type*} [Fintype ι] (p q : ι → ℝ)
    (hp0 : ∀ k, 0 ≤ p k) (hp1 : ∑ k, p k = 1)
    (hq0 : ∀ k, 0 ≤ q k) (hq1 : ∑ k, q k = 1)
    (hsupp : ∀ k, 0 < p k → 0 < q k) :
    (∑ k, p k * Real.log (q k) ≤ ∑ k, p k * Real.log (p k)) ∧
      (∑ k, p k * Real.log (q k) = ∑ k, p k * Real.log (p k) ↔ ∀ k, p k = q k) := by sorry

end FuchsThesis.Coding
