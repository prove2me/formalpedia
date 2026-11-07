-- Prove2me | Theorems.Thm_OnlineCAP_theorem_1_6
-- name    : OnlineCAP.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:27:37.761462+00:00
-- url     : https://prove2.me/theorems/51e1e2f2-70eb-4611-a40b-81a9f2a6d047
-- title:
--   Theorem 1.6 — randomized O(log |P| log log |P|)-competitive weighted online TL-rectangle hitting set
-- statement:
--   There is a function $\alpha(m)=O(\log m\,\log\log m)$ such that for every finite point set $P\subseteq\mathbb R^2$ with $m=|P|$ and every nonnegative cost function on $P$, online hitting set on $P$ in which every arriving shape is the union of a leftless and a topless rectangle has a randomized online algorithm that is feasible for every outcome of its coins and $\alpha(m)$-competitive in expectation against an oblivious adversary.
--
--   The paper proves it by combining an $O(\log m)$-competitive online fractional algorithm for hitting set [Alo+09] with the rounding of Theorem 4.1.
--
--   Differences from the source:
--   - reading: online hitting set with P points (costs not mentioned) → the weighted problem, every cost function c ≥ 0 on P; reason: the next sentence (p.3) places it in "general weighted geometric online hitting set" and §4, which proves it, is weighted; unit costs are a special case, so this is the stronger reading
--   - encoding: O(log |P| log log |P|)-competitive → α : ℕ → ℝ with α =O[atTop] log m · log log m and ratio α(|P|) in expectation against the integral optimum; reason: one function of |P| for all instances; natural logarithms
-- source:
--   Hathcock, Subramanian, Umboh, Zlatin, Weighted and Unweighted Online Connectivity Augmentation via Geometric Hitting Set (manuscript of Nov. 3, 2026, sha256 e3b9cb64…), Theorem 1.6, p.3 (proof §4 and p.13)

import Mathlib
import Definitions.Def_OnlineCAP_RandOnlineAlg
import Definitions.Def_OnlineCAP_OnlineHSInstance
import Definitions.Def_OnlineCAP_OnlineHSInstance_OPT
import Definitions.Def_OnlineCAP_IsCompetitive
import Definitions.Def_OnlineCAP_IsLeftless
import Definitions.Def_OnlineCAP_IsTopless
import Definitions.Def_OnlineCAP_IsTLShape
import Definitions.Def_OnlineCAP_tlInstance

open MeasureTheory Filter Asymptotics

namespace OnlineCAP

/-- **Theorem 1.6 (weighted online TL-rectangle hitting set).** Hathcock–Subramanian–Umboh–Zlatin, *Weighted and Unweighted Online Connectivity
Augmentation via Geometric Hitting Set*, manuscript of Nov. 3, 2026 (sha256 e3b9cb64…), Theorem 1.6, p.3 (PDF p.3):
"There is a randomized O(log |P| log log |P|) competitive algorithm for online hitting set with P
points where each arriving shape is the union of a leftless rectangle and a topless rectangle."

There is a function `α(m) = O(log m · log log m)` such that for every finite point set `P ⊆ ℝ²`
with `m = |P|` and every nonnegative cost function on `P`, the weighted online TL-rectangle hitting
set problem on `P` has a randomized online algorithm that is `α(m)`-competitive in expectation
against an oblivious adversary.

**Formalization Note.** The weighted problem (Problem 1.9, weighted case): the sentence after the
theorem (p.3) and §4, which proves it, are about weighted hitting set; unit costs are a special
case. -/
theorem theorem_1_6 : ∃ α : ℕ → ℝ,
    α =O[atTop] (fun m : ℕ => Real.log m * Real.log (Real.log m)) ∧
    ∀ (P : Finset (ℝ × ℝ)) (c : ℝ × ℝ → ℝ), (∀ p ∈ P, 0 ≤ c p) →
      ∃ A : RandOnlineAlg (ℝ × ℝ) (Set (ℝ × ℝ)), IsCompetitive (tlInstance P c) A (α P.card) := by sorry

end OnlineCAP
