-- Prove2me | Theorems.Thm_MomentSearch_Supplement_theorem_27
-- name    : MomentSearch.Supplement.theorem_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:36:44.661557+00:00
-- url     : https://prove2.me/theorems/9727232d-59ab-40a8-b77b-bd99885c821a
-- title:
--   Theorem 27 — a dyadic JL sketch of dimension $O(\log^4 n/\delta^2)$ recovers every CDF within $\delta$
-- statement:
--   There is an absolute constant $C>0$ such that for every $n\ge2$ and every $\delta\in(0,1)$ there exist an integer $k\le C\log_2^4 n/\delta^2$ and matrices $U\in\mathbb R^{n\times k}$, $V\in\mathbb R^{k\times n}$ such that every distribution $p\in\Delta_n$ satisfies
--   $$\|U(Vp)-P\|_\infty\le\delta,$$
--   where $P$ is the CDF of $p$.
--
--   The matrices are deterministic and work for all distributions simultaneously. Combined with Coarse Greedy this gives linear sketches of dimension $\tilde O(n^{\varepsilon})$ with approximability factor $O(1/\varepsilon)$ (Corollary 21).
--
--   Differences from the source:
--   - encoding: k = O(log⁴ n/δ²) → ∃ k : ℕ with k ≤ C·log₂⁴ n/δ², C absolute and chosen before n and δ; reason: O(·) hides an absolute constant
--   - encoding: ‖U(Vp) − P‖_∞ ≤ δ → |(U(Vp))_t − P(t)| ≤ δ for every t ∈ [n]₀; reason: definition of the sup norm on ℝ^n
--   - encoding: distributions p ∈ Δ_n → n ≥ 2 as a hypothesis; reason: the paper's standing assumption n ≥ 2 (§2.1)
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 27, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_MomentSearch_Supplement_cdf

namespace MomentSearch.Supplement

/-- **Theorem 27** (Dyadic JL sketch for CDF approximation) (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), Theorem 27, p.35 (PDF p.37)).

There is an absolute constant `C > 0` such that for every `n ≥ 2` and every `δ ∈ (0, 1)` there
are an integer `k ≤ C · log⁴ n / δ²` and matrices `U ∈ ℝ^{n×k}`, `V ∈ ℝ^{k×n}` such that every
distribution `p ∈ Δ_n` satisfies `‖U(Vp) − P‖_∞ ≤ δ`, where `P` is the CDF of `p`.

**Formalization Note.** `k = O(log⁴ n/δ²)` is `k ≤ C log₂⁴ n / δ²` with `C` absolute, chosen
before `n` and `δ`. The matrices are deterministic and work for all `p ∈ Δ_n` simultaneously.
The sup norm is written coordinatewise over `t ∈ [n]₀`. -/
theorem theorem_27 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ), 2 ≤ n → ∀ δ : ℝ, 0 < δ → δ < 1 →
        ∃ k : ℕ, (k : ℝ) ≤ C * Real.logb 2 n ^ 4 / δ ^ 2 ∧
          ∃ (U : Matrix (Fin n) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ),
            ∀ p ∈ stdSimplex ℝ (Fin n), ∀ t : Fin n,
              |Matrix.mulVec U (Matrix.mulVec V p) t - cdf p (t : ℕ)| ≤ δ := by sorry

end MomentSearch.Supplement
