-- Prove2me | Theorems.Thm_OnlineCAP_theorem_4_12
-- name    : OnlineCAP.theorem_4_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:26:10.134755+00:00
-- url     : https://prove2.me/theorems/8e7fb74a-de4c-43a9-8b24-f66bf16e5b2d
-- title:
--   Theorem 4.12 — rounding for unions loses 2(α₁(n) + α₂(n)) (corrected: α₁(n), α₂(n) ≥ 0 or no empty request)
-- statement:
--   Let $U$ be a finite universe of $n$ elements, $\mathcal F_1,\mathcal F_2$ families of subsets of $U$, and $\mathcal F_3=\{S_1\cup S_2:S_1\in\mathcal F_1,S_2\in\mathcal F_2\}$. Let $\alpha_1,\alpha_2\in\mathbb R$ with $\alpha_1,\alpha_2\ge0$, or else assume that neither $\mathcal F_1$ nor $\mathcal F_2$ contains the empty set. If $\mathcal F_1$ has an $\alpha_1$-rounding algorithm and $\mathcal F_2$ has an $\alpha_2$-rounding algorithm, then $\mathcal F_3$ has a
--   $$2(\alpha_1+\alpha_2)\text{-rounding algorithm}.$$
--
--   Applied to leftless and topless rectangles this gives a rounding algorithm for TL shapes with the same $O(\log\log n)$ loss up to a constant.
--
--   **Formalization Note** $\alpha_1,\alpha_2$ are the values $\alpha_1(n),\alpha_2(n)$ at $n=|U|$.
--
--   Differences from the source:
--   - correction: α₁(n)-, α₂(n)-rounding algorithms (no sign condition, families of arbitrary subsets) → α₁, α₂ ≥ 0, or ∅ ∉ F₁ and ∅ ∉ F₂; reason: under the standing assumption of Problem 2.4 (p.9, "F is a family of non-empty subsets of U") the printed statement holds, and the alternative α₁, α₂ ≥ 0 covers families containing ∅ (the topless and leftless traces of the proof of Theorem 4.1); without either the printed statement is false for negative values: with F₁ = {∅} every algorithm is an α₁-rounding algorithm for every α₁ (no input can be fractionally covered, so no nonempty input is valid); take α₁ = −1, U = {u}, F₂ = {{u}} with the 1-rounding algorithm "buy u at the first request", α₂ = 1; then F₃ = {{u}} would need a 0-rounding algorithm, i.e. Pr[u ∈ H₁] ≤ 0 on the valid input ({u}, x ≡ 1) while H₁ must contain u
--   - encoding: α₁(n), α₂(n) functions of n = |U| → the two real numbers α₁(|U|), α₂(|U|) for the fixed universe; reason: U is fixed in the statement
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 4.12, p.21

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_IsRounding
import Definitions.Def_OnlineCAP_unionFam

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Theorem 4.12 (rounding for unions) (corrected: α₁(n), α₂(n) ≥ 0 or no empty request).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 4.12, p.21
(PDF p.21): "Let U be a universe of n elements. Suppose F1 and F2 are two families of subsets of U,
and let F3 = {S1 ∪ S2 : S1 ∈ F1, S2 ∈ F2}. Furthermore, suppose that A1 is an α1(n)-rounding
algorithm for F1 and A2 is an α2(n)-rounding algorithm for F2. Then, there is a
2(α1(n) + α2(n))-rounding algorithm for F3."

For a finite universe `U` and families `F₁, F₂`: if `F₁` has an `α₁`-rounding algorithm and `F₂`
an `α₂`-rounding algorithm, and either `α₁, α₂ ≥ 0` or neither family contains the empty set,
then `F₃ = {S₁ ∪ S₂}` has a `2(α₁ + α₂)`-rounding
algorithm.

**Formalization Note.** `α₁, α₂` are the numbers `α₁(n), α₂(n)` for `n = |U|`. A hypothesis
is added, because without one the statement is false: with `F₁ = {∅}` every algorithm is an `α₁`-rounding algorithm for every
`α₁` (no request can be fractionally covered), so `α₁ = −1`, `α₂ = 1`, `U` a single element `u`
and `F₂ = {{u}}` would demand a `0`-rounding algorithm for `F₃ = {{u}}`, which does not exist.
The alternative `∅ ∉ F₁, F₂` is the standing assumption of online hitting set (Problem 2.4, p.9:
"F is a family of non-empty subsets of U"), under which the printed statement holds as written;
the alternative `α₁, α₂ ≥ 0` covers families containing `∅`, such as the traces of topless and
leftless rectangles used in the proof of Theorem 4.1. -/
theorem theorem_4_12 (U : Type) [Fintype U] (F₁ F₂ : Set (Set U)) (α₁ α₂ : ℝ)
    (hα : (0 ≤ α₁ ∧ 0 ≤ α₂) ∨ (∅ ∉ F₁ ∧ ∅ ∉ F₂))
    (hA₁ : ∃ A₁ : RandOnlineAlg U (Set U × (U → ℝ)), IsRounding F₁ A₁ α₁)
    (hA₂ : ∃ A₂ : RandOnlineAlg U (Set U × (U → ℝ)), IsRounding F₂ A₂ α₂) :
    ∃ A : RandOnlineAlg U (Set U × (U → ℝ)), IsRounding (unionFam F₁ F₂) A (2 * (α₁ + α₂)) := by sorry

end OnlineCAP
