-- Prove2me | Theorems.Thm_MomentSearch_Supplement_theorem_6
-- name    : MomentSearch.Supplement.theorem_6
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T09:32:51.72572+00:00
-- url     : https://prove2.me/theorems/ef524cc7-4009-4fe4-b0a7-6186b21af76e
-- title:
--   Theorem 6 — sketches of $\tfrac12 n^{\varepsilon}\log n$ bits have approximability factor at least $\gamma/\varepsilon$
-- statement:
--   There is a universal constant $\gamma>0$ such that for every fixed $\varepsilon\in(0,1/4)$ there exists $n_0(\varepsilon)$ with the following property for all $n\ge n_0(\varepsilon)$. Let $\sigma:\Delta_n\to X$ be a sketch that can be encoded with at most $\tfrac12 n^{\varepsilon}\log_2 n$ bits, that is, its image $\sigma(\Delta_n)$ is finite and has at most $2^k$ elements for some integer $k\le\tfrac12 n^{\varepsilon}\log_2 n$. Then its uncertainty collection $\mathcal U_\sigma$ (the nonempty fibres $\{p\in\Delta_n:\sigma(p)=x\}$) satisfies
--   $$\alpha(\mathcal U_\sigma)\ge\frac{\gamma}{\varepsilon}.$$
--
--   The bound applies to every encoding of the distribution, including encodings of search strategies, and is matched by quantile sketches (Theorem 8).
--
--   Differences from the source:
--   - encoding: a sketch σ : Δ_n → X that can be encoded with at most ½ n^ε log n bits → σ : (Fin n → ℝ) → X for a type X, with σ '' Δ_n finite and of cardinality ≤ 2^k for some k : ℕ with k ≤ ½ n^ε log₂ n; reason: §3.1 (p.7): a sketch can be encoded with k bits if X = σ(Δ_n) is finite and |X| ≤ 2^k; values off the simplex play no role since every fibre is intersected with Δ_n
--   - reading: for a universal constant γ > 0 → ∃ γ > 0 chosen before ε, n₀ and n; reason: universal means independent of ε, n and σ; only n₀ depends on ε
-- source:
--   Megow, Stein, Verschae, Distributionally Robust Search: The Power of Information and the Limits of Moments, arXiv:2611.04559 (held version, sha256 fbfa4b43350dfaea073a9c0a9a0850a9955ea82082a7163a2db90cc48b9339e3), Theorem 6, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_MomentSearch_approxFactor
import Definitions.Def_MomentSearch_sketchCollection

open scoped ENNReal

namespace MomentSearch.Supplement

open MomentSearch

/-- **Theorem 6** (Information-theoretic lower bound) (Megow, Stein, Verschae, *Distributionally Robust Search: The Power of Information and the Limits of Moments*, arXiv:2611.04559 (held version, sha256 fbfa4b43…), Theorem 6, p.8 (PDF p.10)).

There is a universal constant `γ > 0` such that for every fixed `ε ∈ (0, 1/4)` there is
`n₀(ε)` with the following property for all `n ≥ n₀(ε)`: if a sketch `σ : Δ_n → X` can be
encoded with at most `½ n^ε log₂ n` bits, i.e. its image `σ(Δ_n)` is finite and has at most
`2^k` elements for some integer `k ≤ ½ n^ε log₂ n`, then `α(𝒰_σ) ≥ γ/ε`.

**Formalization Note.** "Encoded with `k` bits" is the paper's `|X| ≤ 2^k` for `X = σ(Δ_n)`
finite (§3.1, p.7). The sketch is a map on all of `ℝ^n` into an arbitrary type `X`; only its
values on the simplex matter. `γ` is chosen before `ε`; only `n₀` depends on `ε`. -/
theorem theorem_6 :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 4 →
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          ∀ (X : Type) (σ : (Fin n → ℝ) → X) (k : ℕ),
            (k : ℝ) ≤ 1 / 2 * (n : ℝ) ^ ε * Real.logb 2 n →
            (σ '' stdSimplex ℝ (Fin n)).Finite →
            (σ '' stdSimplex ℝ (Fin n)).ncard ≤ 2 ^ k →
            ENNReal.ofReal (γ / ε) ≤ approxFactor (sketchCollection σ) := by sorry

end MomentSearch.Supplement
