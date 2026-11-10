-- Prove2me | Theorems.Thm_MomentSearch_lemma_11
-- name    : MomentSearch.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:09:50.208509+00:00
-- url     : https://prove2.me/theorems/74d52243-514e-4032-993c-b8dd99fa8a6b
-- title:
--   Lemma 11 — signed corrections give two distributions with the same moments
-- statement:
--   Let $n\ge2$, $k\ge0$, $m,m_0\in[n]_0$, and let $a\in\mathbb R^n$ solve the signed-correction system
--
--   $$
--   \sum_{t=0}^{n-1} a_t\,\tau_t^i=\tau_m^i-\tau_{m_0}^i\qquad (i=0,\dots,k).
--   $$
--
--   Then there are two distributions $p,p'\in\Delta_n$ with the same first $k$ moments ($\mu_i(p)=\mu_i(p')$ for $i=0,\dots,k$) such that
--
--   $$
--   p_m\ \ge\ 1-\tfrac12\|a\|_1\qquad\text{and}\qquad p'_{m_0}\ \ge\ 1-\tfrac12\|a\|_1 .
--   $$
--
--   It reduces the construction of moment-matching distributions with separated peaks to finding a signed correction of small $\ell_1$-norm.
--
--   Differences from the source:
--   - encoding: m, m₀ ∈ [n]₀ and a ∈ ℝⁿ → m m₀ : Fin n and a : Fin n → ℝ; reason: Lean convention; same instances
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, Lemma 11, p.11 (PDF p.13); restated App. C.1, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MomentSearch_moment
import Definitions.Def_MomentSearch_SolvesCorrection

namespace MomentSearch

/-- **Lemma 11** (signed corrections and distributions), Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, p.11 (PDF p.13);
restated App. C.1, p.21 (PDF p.23).

Let `m, m₀ ∈ [n]₀`. If `a` solves Equation (3) (`∑_t a_t τ_t^i = τ_m^i − τ_{m₀}^i`, `i = 0, …, k`),
then there are two distributions `p, p'` on `[n]₀` with the same first `k` moments and
`p_m, p'_{m₀} ≥ 1 − ½‖a‖₁`.

**Formalization Note.** Distributions are points of `stdSimplex ℝ (Fin n)`; "the same first `k`
moments" is `µ_i(p) = µ_i(p')` for `i = 0, …, k`; `‖a‖₁ = ∑_t |a_t|`; `n ≥ 2` is the paper's
standing assumption (§2.1). -/
theorem lemma_11 {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (m m₀ : Fin n) (a : Fin n → ℝ)
    (ha : SolvesCorrection n k m m₀ a) :
    ∃ p p' : Fin n → ℝ, p ∈ stdSimplex ℝ (Fin n) ∧ p' ∈ stdSimplex ℝ (Fin n) ∧
      (∀ i : ℕ, i ≤ k → moment p i = moment p' i) ∧
      1 - (1 / 2) * ∑ t : Fin n, |a t| ≤ p m ∧
      1 - (1 / 2) * ∑ t : Fin n, |a t| ≤ p' m₀ := by sorry

end MomentSearch
