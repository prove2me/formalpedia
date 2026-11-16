-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_Supplement_construction_count
-- name    : MajorityDepthThree.Exact.Supplement.construction_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:17:17.749125+00:00
-- url     : https://prove2.me/theorems/509123d2-c07a-4234-91c0-0fa1b685086a
-- title:
--   Fact 3.8 — exact $\theta_t(P^3_{s,t})$ (corrected: odd case excludes (s,t) = (1,1))
-- statement:
--   For an integer $s$ and a natural number $t$, let $V=\{0,\dots,3t-s-1\}$ and let $\theta_t(P^3_{s,t})$ be the number of satisfying assignments of the construction $P^3_{s,t}$ on $V$ with exactly $t$ variables set to one. Then
--
--   $$\theta_t(P^3_{s,t})=\begin{cases}3^t & s\le0,\ t\ge0,\\ \left(\tfrac23\right)^{s/2}3^t & s\text{ even},\ 1\le s\le t,\\ \tfrac79\left(\tfrac23\right)^{(s-1)/2}3^t & s\text{ odd},\ 1\le s\le t,\ (s,t)\ne(1,1).\end{cases}$$
--
--   These are exact equalities of real numbers. They give the lower bounds of Theorem 3.10 for the monotone maximum $\Phi_0(s,t)$ via the witness of Fact 3.7.
--
--   Differences from the source:
--   - correction: odd case for all 1 ≤ s ≤ t → odd case for 1 ≤ s ≤ t except (s,t) = (1,1); reason: at s = t = 1 the printed value is 7/3, not an integer, so no count can equal it; P^3_{1,1} is moreover undefined
--   - encoding: n = 3t − s variables → the variable set {0, …, 3t − s − 1} ⊂ ℕ, with 3t − s computed in ℤ; reason: relabeling changes no count; on the stated ranges 3t − s ≥ 0
--   - encoding: exponents s/2 and (s − 1)/2 → natural-number exponents (toNat s)/2 and (toNat s − 1)/2; reason: in their cases s ≥ 1 and the divisions are exact
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.9, Fact 3.8

import Definitions.Def_MajorityDepthThree_Exact_Supplement_Constructions

set_option autoImplicit false

namespace MajorityDepthThree.Exact.Supplement

open MajorityDepthThree.Exact

/-- Fact 3.8 (p. 9): the exact number of `t`-transversals of `P^3_{s,t}` on the
variables `range (3t - s)`. Corrected: the odd case excludes `(s,t) = (1,1)`, where
the printed value `7/3` is not an integer (and `P^3_{1,1}` is undefined). -/
theorem construction_count :
    (∀ (s : ℤ) (t : ℕ), s ≤ 0 →
      (theta (Finset.range (3 * (t : ℤ) - s).toNat) (P3 s t) t : ℝ) = 3 ^ t) ∧
    (∀ (s : ℤ) (t : ℕ), Even s → 1 ≤ s → s ≤ t →
      (theta (Finset.range (3 * (t : ℤ) - s).toNat) (P3 s t) t : ℝ) =
        (2 / 3 : ℝ) ^ (s.toNat / 2) * 3 ^ t) ∧
    (∀ (s : ℤ) (t : ℕ), Odd s → 1 ≤ s → s ≤ t → ¬ (s = 1 ∧ t = 1) →
      (theta (Finset.range (3 * (t : ℤ) - s).toNat) (P3 s t) t : ℝ) =
        (7 / 9 : ℝ) * (2 / 3 : ℝ) ^ ((s.toNat - 1) / 2) * 3 ^ t) := by sorry

end MajorityDepthThree.Exact.Supplement
