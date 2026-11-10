-- Prove2me | Theorems.Thm_MomentSearch_lemma_14
-- name    : MomentSearch.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:10:52.421585+00:00
-- url     : https://prove2.me/theorems/ab16dd15-1b2e-4840-bfad-47c6ed727f5b
-- title:
--   Lemma 14 — bound on the correction value $\gamma^*(m,m_0)$
-- statement:
--   Let $C_1$ be a constant with the property of Lemma 13: for all $n\ge2$, all $k\le(n-1)/2$ and all real polynomials $q$ with $\deg q\le k$ and $|q(\tau_t)|\le1$ for $t\in[n]_0$, one has $|q|\le C_1$ on $[-3/4,3/4]$. Let $1\le k\le (n-1)/2$ and let $m,m_0\in[n]_0\cap\bigl[\frac{n-1}4,\frac{3(n-1)}4\bigr]$. Then
--
--   $$
--   \gamma^*(m,m_0)\ \le\ \frac{8C_1}{\sqrt5}\cdot\frac{k\,|m-m_0|}{n-1}.
--   $$
--
--   Together with Lemma 11 this gives Proposition 10.
--
--   Differences from the source:
--   - generalization: C₁ is the constant of Lemma 13 (the paper's C₁ = C₀ log(π/arctan(√3/2))) → every C₁ satisfying Lemma 13's conclusion; reason: the paper's C₁ satisfies the hypothesis, so the statement specializes to the page; the proof uses only Lemma 13's bound
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, Lemma 14, p.12 (PDF p.14); restated App. C.1, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_MomentSearch_correctionNorm

namespace MomentSearch

/-- **Lemma 14**, Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, p.12 (PDF p.14); restated App. C.1, p.24 (PDF p.26).

Let `1 ≤ k ≤ (n − 1)/2` and let `m, m₀ ∈ [n]₀ ∩ [(n−1)/4, 3(n−1)/4]`. Then
`γ*(m, m₀) ≤ (8C₁/√5) · k|m − m₀|/(n − 1)`, where `C₁` is the constant of Lemma 13.

**Formalization Note.** "The constant of Lemma 13" is any `C₁` satisfying Lemma 13's
conclusion (hypothesis `hC₁`, Lemma 13's statement verbatim); the paper's
`C₁ = C₀ log(π/arctan(√3/2))` is one such constant, so this specializes to the page. -/
theorem lemma_14 (C₁ : ℝ)
    (hC₁ : ∀ n k : ℕ, 2 ≤ n → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
      ∀ q : Polynomial ℝ, q.natDegree ≤ k →
      (∀ t : Fin n, |q.eval (grid n (t : ℕ))| ≤ 1) →
      ∀ x ∈ Set.Icc (-(3 / 4 : ℝ)) (3 / 4), |q.eval x| ≤ C₁)
    (n k : ℕ) (hk1 : 1 ≤ k) (hk : (k : ℝ) ≤ ((n : ℝ) - 1) / 2) (m m₀ : Fin n)
    (hm : ((n : ℝ) - 1) / 4 ≤ ((m : ℕ) : ℝ) ∧ ((m : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4)
    (hm₀ : ((n : ℝ) - 1) / 4 ≤ ((m₀ : ℕ) : ℝ) ∧ ((m₀ : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4) :
    correctionNorm n k m m₀ ≤
      8 * C₁ / Real.sqrt 5 * ((k : ℝ) * |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| / ((n : ℝ) - 1)) := by sorry

end MomentSearch
