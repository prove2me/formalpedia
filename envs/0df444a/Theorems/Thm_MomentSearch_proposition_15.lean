-- Prove2me | Theorems.Thm_MomentSearch_proposition_15
-- name    : MomentSearch.proposition_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:00.352793+00:00
-- url     : https://prove2.me/theorems/e256b116-820f-4e1c-ac3b-e207bdb12147
-- title:
--   Proposition 15 — several distributions with matching moments
-- statement:
--   There is a constant $C>0$ such that both of the following hold.
--
--   1. (Proposition 10 with this $C$.) For integers $n\ge3$, $1\le k\le(n-1)/2$ and $m,m_0\in[n]_0\cap\bigl[\frac{n-1}4,\frac{3(n-1)}4\bigr]$ there are distributions $p,p'$ on $[n]_0$ and $\gamma\le C\frac{k}{n-1}|m-m_0|$ with $p_m,p'_{m_0}\ge1-\gamma$ and $\mu_i(p)=\mu_i(p')$ for $i=0,\dots,k$.
--   2. Let $n\ge3$, $1\le k\le(n-1)/2$, $R\ge0$, and let $m_0,m_1,\dots,m_R\in\bigl[\frac{n-1}4,\frac{3(n-1)}4\bigr]\cap[n]_0$. Then there exist distributions $p^{(0)},\dots,p^{(R)}$ on $[n]_0$ with the same first $k$ moments and $p^{(r)}_{m_r}\ge1-\gamma$ for all $r=0,\dots,R$, where
--
--   $$
--   \gamma\ \le\ C\,\frac{k}{n-1}\sum_{s=1}^{R}|m_s-m_0| .
--   $$
--
--   The family of moment-matching distributions with peaks at prescribed positions feeds the search lower bound of Theorem 16.
--
--   Differences from the source:
--   - reading: Let C be the constant of Proposition 10 → one C > 0 for which Proposition 10's conclusion and Proposition 15's conclusion both hold; reason: drafts cannot import another statement's constant; the proofs use the same C = 4C₁/√5
--   - encoding: peaks m₀,…,m_R ∈ [n]₀ and distributions p⁽⁰⁾,…,p⁽ᴿ⁾ → sequences m : ℕ → Fin n and p : ℕ → (Fin n → ℝ), used at indices 0,…,R; same moments as p⁽⁰⁾; reason: Lean convention; same instances
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, Proposition 15, p.12 (PDF p.14); restated App. C.2, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_MomentSearch_moment

namespace MomentSearch

/-- **Proposition 15** (several distributions with matching moments), Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, p.12
(PDF p.14); restated App. C.2, p.25 (PDF p.27).

Let `n ≥ 3` and `1 ≤ k ≤ (n − 1)/2`, and let `m₀, m₁, …, m_R ∈ [(n−1)/4, 3(n−1)/4] ∩ [n]₀`.
Let `C` be the constant of Proposition 10. Then there exist distributions `p⁽⁰⁾, …, p⁽ᴿ⁾` on
`[n]₀` with the same first `k` moments and `p⁽ʳ⁾_{m_r} ≥ 1 − γ` for all `r = 0, …, R`, where
`γ ≤ C (k/(n − 1)) ∑_{s=1}^{R} |m_s − m₀|`.

**Formalization Note.** "The constant of Proposition 10" is read as: there is one `C > 0` for
which Proposition 10's conclusion (first conjunct, verbatim) and Proposition 15's conclusion
(second conjunct) both hold. The peaks are a sequence `m : ℕ → Fin n` of which `m 0, …, m R` are
used, and the distributions a sequence `p : ℕ → (Fin n → ℝ)`; the peaks need not be distinct. -/
theorem proposition_15 :
    ∃ C : ℝ, 0 < C ∧
      (∀ n k : ℕ, 3 ≤ n → 1 ≤ k → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
        ∀ m m₀ : Fin n,
          ((n : ℝ) - 1) / 4 ≤ ((m : ℕ) : ℝ) → ((m : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 →
          ((n : ℝ) - 1) / 4 ≤ ((m₀ : ℕ) : ℝ) → ((m₀ : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4 →
          ∃ p p' : Fin n → ℝ, ∃ γ : ℝ,
            p ∈ stdSimplex ℝ (Fin n) ∧ p' ∈ stdSimplex ℝ (Fin n) ∧
            γ ≤ C * ((k : ℝ) / ((n : ℝ) - 1)) * |((m : ℕ) : ℝ) - ((m₀ : ℕ) : ℝ)| ∧
            1 - γ ≤ p m ∧ 1 - γ ≤ p' m₀ ∧
            ∀ i : ℕ, i ≤ k → moment p i = moment p' i) ∧
      (∀ n k : ℕ, 3 ≤ n → 1 ≤ k → (k : ℝ) ≤ ((n : ℝ) - 1) / 2 →
        ∀ (R : ℕ) (m : ℕ → Fin n),
          (∀ r : ℕ, r ≤ R → ((n : ℝ) - 1) / 4 ≤ ((m r : ℕ) : ℝ) ∧
            ((m r : ℕ) : ℝ) ≤ 3 * ((n : ℝ) - 1) / 4) →
          ∃ p : ℕ → Fin n → ℝ, ∃ γ : ℝ,
            (∀ r : ℕ, r ≤ R → p r ∈ stdSimplex ℝ (Fin n)) ∧
            (∀ r : ℕ, r ≤ R → ∀ i : ℕ, i ≤ k → moment (p r) i = moment (p 0) i) ∧
            γ ≤ C * ((k : ℝ) / ((n : ℝ) - 1)) *
              ∑ s ∈ Finset.Icc 1 R, |((m s : ℕ) : ℝ) - ((m 0 : ℕ) : ℝ)| ∧
            ∀ r : ℕ, r ≤ R → 1 - γ ≤ p r (m r)) := by sorry

end MomentSearch
