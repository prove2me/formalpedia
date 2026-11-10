-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_6_1
-- name    : OptStochMatch.Tight.lemma_6_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:56:51.421554+00:00
-- url     : https://prove2.me/theorems/1ef16001-663d-4dbb-8626-73a5d35eedab
-- title:
--   Lemma 6.1 — balanced rates dominate every capped feasible allocation
-- statement:
--   Let $s$ be given by (6.1) for the unmatched set $A$. Let $x_i\ge0$, $c\ge0$, and let $y\in\mathcal P_\lambda$ be supported on $A$ with $y_i\le x_i+c$. For every nonincreasing $w:[0,\infty)\to[0,1]$ with $w(0)=1$,
--   $$\sum_{i\in A}\big[w(x_i)s_i+(1-w(x_i))(x_i+c)\big]\ge\sum_{i\in A}y_i.\qquad(6.2)$$
--
--   Differences from the source:
--   - encoding: w : [0,∞) → [0,1] nonincreasing → w : ℝ → ℝ, antitone on [0,∞), with values in [0,1] on [0,∞); reason: only values on [0,∞) are used; same class of functions
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 6.1, eq. (6.2), p. 27 (PDF p. 28)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Basic
import Definitions.Def_OptStochMatch_Tight_Matching
import Definitions.Def_OptStochMatch_Tight_Algorithms
open scoped NNReal BigOperators

namespace OptStochMatch.Tight

/-- Lemma 6.1 (p. 27, PDF 28). Let `s` be given by (6.1) for the unmatched set `A`. Let
`x_i ≥ 0` and `c ≥ 0`, and let `y ∈ P_λ` be supported on `A` with `y_i ≤ x_i + c`. For every
nonincreasing `w : [0, ∞) → [0, 1]` with `w(0) = 1`,
`∑_{i∈A} [w(x_i) s_i + (1 − w(x_i))(x_i + c)] ≥ ∑_{i∈A} y_i` (6.2). -/
theorem lemma_6_1 {m : ℕ} (lam : Ty m → ℝ≥0) (A : Finset (Fin m)) (s : Fin m → ℝ)
    (hs : IsBalanced lam A s) (x : Fin m → ℝ) (hx : ∀ i, 0 ≤ x i) (c : ℝ) (hc : 0 ≤ c)
    (y : Fin m → ℝ) (hy : y ∈ Plam lam) (hyA : ∀ i, i ∉ A → y i = 0)
    (hyx : ∀ i, y i ≤ x i + c) (w : ℝ → ℝ) (hw_anti : AntitoneOn w (Set.Ici 0))
    (hw_range : ∀ z, 0 ≤ z → 0 ≤ w z ∧ w z ≤ 1) (hw0 : w 0 = 1) :
    ∑ i ∈ A, y i ≤ ∑ i ∈ A, (w (x i) * s i + (1 - w (x i)) * (x i + c)) := by sorry

end OptStochMatch.Tight
