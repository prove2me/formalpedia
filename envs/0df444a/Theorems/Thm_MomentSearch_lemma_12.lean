-- Prove2me | Theorems.Thm_MomentSearch_lemma_12
-- name    : MomentSearch.lemma_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:11:08.652191+00:00
-- url     : https://prove2.me/theorems/d8622f41-e036-45b5-a2cb-b730d5eaba93
-- title:
--   Lemma 12 — LP dual of the signed correction
-- statement:
--   Let $n\ge2$ and $k\ge0$. For all $m,m_0\in[n]_0$,
--
--   $$
--   \gamma^*(m,m_0)=\max\Bigl\{\,q(\tau_m)-q(\tau_{m_0})\ :\ q \text{ a real polynomial with } \deg q\le k \text{ and } |q(\tau_t)|\le1 \text{ for all } t\in[n]_0\Bigr\}.
--   $$
--
--   Moreover, the infimum defining $\gamma^*(m,m_0)$ is attained: some solution $a$ of the correction system has $\|a\|_1=\gamma^*(m,m_0)$.
--
--   The lemma turns the bound on the correction value into a bound on increments of polynomials that are bounded by $1$ on the grid.
--
--   Differences from the source:
--   - encoding: γ* equals the maximum of the set of increments → γ* is the greatest element of that set (IsGreatest); reason: same meaning: the maximum exists and equals γ*
--   - encoding: deg q ≤ k → q.natDegree ≤ k; reason: Lean convention; both admit the zero polynomial
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, Lemma 12, p.11 (PDF p.13); restated App. C.1, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_MomentSearch_correctionNorm

namespace MomentSearch

/-- **Lemma 12** (dual of the signed correction), Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), §4.1, p.11 (PDF p.13); restated
App. C.1, p.22 (PDF p.24).

For all `m, m₀ ∈ [n]₀`,
`γ*(m, m₀) = max { q(τ_m) − q(τ_{m₀}) : q a polynomial with deg q ≤ k and |q(τ_t)| ≤ 1 for all t ∈ [n]₀ }`.
Moreover, the infimum in Equation (4) is attained.

**Formalization Note.** "max" is `IsGreatest`: `γ*` belongs to the set of increments and bounds
it above. "deg q ≤ k" is `q.natDegree ≤ k`, which admits the zero polynomial. Attainment is an
`a` solving (7) with `‖a‖₁ = γ*`. `n ≥ 2` is the standing assumption (§2.1). -/
theorem lemma_12 {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (m m₀ : Fin n) :
    IsGreatest
      {y : ℝ | ∃ q : Polynomial ℝ, q.natDegree ≤ k ∧
        (∀ t : Fin n, |q.eval (grid n (t : ℕ))| ≤ 1) ∧
        y = q.eval (grid n (m : ℕ)) - q.eval (grid n (m₀ : ℕ))}
      (correctionNorm n k m m₀) ∧
    ∃ a : Fin n → ℝ, SolvesCorrection n k m m₀ a ∧
      ∑ t : Fin n, |a t| = correctionNorm n k m m₀ := by sorry

end MomentSearch
