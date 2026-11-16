-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_Supplement_deficit_profile
-- name    : MajorityDepthThree.Exact.Supplement.deficit_profile
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:18:27.88319+00:00
-- url     : https://prove2.me/theorems/b0c40a92-9373-4958-88e7-35beab9ce4e8
-- title:
--   Theorem 3.10 — deficit profile of $\Phi_0(s,t)$ (corrected: odd bound excludes (s,t) = (1,1))
-- statement:
--   For an integer deficit $s$ and a natural number $t$, let $n=3t-s$. Write $\Phi_0(s,t)$ for the maximum number of $t$-transversals (satisfying assignments with exactly $t$ ones) of a $t$-threshold monotone 3-CNF on $n$ variables, and $\Theta(3t-s,t,3)$ for the same maximum over all $t$-threshold 3-CNFs, negative literals allowed (Definition 3.6 identifies the two). Then
--
--   1. for all $s\le0$, $t\ge0$: $\Phi_0(s,t)=\Theta(3t-s,t,3)=3^t$;
--   2. for all $t\ge1$ and $0\le 2t-2\le s\le 2t$: $\Phi_0(s,t)=\Theta(3t-s,t,3)=\binom{3t-s}{t}$;
--   3. for even $s$ with $1\le s\le t$: $\Phi_0(s,t)\ge\left(\tfrac23\right)^{s/2}3^t$;
--   4. for odd $s$ with $1\le s\le t$ and $(s,t)\neq(1,1)$: $\Phi_0(s,t)\ge\tfrac79\left(\tfrac23\right)^{(s-1)/2}3^t$.
--
--   $$\Phi_0(s,t)=\begin{cases}3^t & s\le 0,\\ \binom{3t-s}{t} & 2t-2\le s\le 2t,\end{cases}\qquad \Phi_0(s,t)\ge\begin{cases}(2/3)^{s/2}3^t & s\text{ even},\\ \tfrac79(2/3)^{(s-1)/2}3^t & s\text{ odd}.\end{cases}$$
--
--   The equalities are exact maxima: line 1 includes the upper bound that no $t$-threshold 3-CNF on at least $3t$ variables has more than $3^t$ transversals of size $t$. At $s=t$ even, $n=2t$, line 3 gives $\Phi_0\ge 6^{t/2}=6^{n/4}$, the lower-bound side of Theorem 1.4 of the mission.
--
--   Differences from the source:
--   - correction: odd lower bound for all 1 ≤ s ≤ t → odd lower bound for 1 ≤ s ≤ t except (s,t) = (1,1); reason: at s = t = 1 it claims Φ0(1,1) ≥ 7/3, but n = 2 and the theorem's own second line gives Φ0(1,1) = binom(2,1) = 2
--   - reading: Φ0(s,t), defined as a maximum over monotone 3-CNFs and "in other words" equal to Θ(3t − s, t, 3) → the equalities stated for both the monotone maximum and the maximum over all signed 3-CNFs, the lower bounds for the monotone maximum; reason: Definition 3.6 gives both descriptions; stating the equalities for both and the lower bounds for the smaller monotone maximum keeps the stronger content of each
--   - encoding: n = 3t − s variables → the carrier Fin (toNat (3t − s)), with 3t − s computed in ℤ; reason: on every stated range 3t − s ≥ t ≥ 0
--   - encoding: exponents s/2 and (s − 1)/2 → natural-number exponents (toNat s)/2 and (toNat s − 1)/2; reason: in their cases s ≥ 1 and the divisions are exact
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.10, Theorem 3.10 (with Definition 3.6, p.9)

import Definitions.Def_MajorityDepthThree_Exact_Supplement_Constructions

set_option autoImplicit false

namespace MajorityDepthThree.Exact.Supplement

open MajorityDepthThree.Exact

/-- Theorem 3.10 (p. 10), the deficit profile of `Φ₀(s,t)`, `n = 3t - s`.
Equalities (1), (2) hold both for the monotone maximum `Φ₀` and for the maximum
`Θ(3t - s, t, 3)` over all signed 3-CNFs (Definition 3.6 identifies the two).
Corrected: the odd lower bound (4) excludes `(s,t) = (1,1)`, where it would claim
`Φ₀(1,1) ≥ 7/3`, contradicting line (2), `Φ₀(1,1) = binom(2,1) = 2`. -/
theorem deficit_profile :
    (∀ (s : ℤ) (t : ℕ), s ≤ 0 → Phi0 s t = 3 ^ t ∧ ThetaDeficit s t = 3 ^ t) ∧
    (∀ (s : ℤ) (t : ℕ), 1 ≤ t → 0 ≤ 2 * (t : ℤ) - 2 → 2 * (t : ℤ) - 2 ≤ s →
      s ≤ 2 * (t : ℤ) →
      Phi0 s t = Nat.choose (3 * (t : ℤ) - s).toNat t ∧
        ThetaDeficit s t = Nat.choose (3 * (t : ℤ) - s).toNat t) ∧
    (∀ (s : ℤ) (t : ℕ), Even s → 1 ≤ s → s ≤ t →
      (2 / 3 : ℝ) ^ (s.toNat / 2) * 3 ^ t ≤ (Phi0 s t : ℝ)) ∧
    (∀ (s : ℤ) (t : ℕ), Odd s → 1 ≤ s → s ≤ t → ¬ (s = 1 ∧ t = 1) →
      (7 / 9 : ℝ) * (2 / 3 : ℝ) ^ ((s.toNat - 1) / 2) * 3 ^ t ≤ (Phi0 s t : ℝ)) := by sorry

end MajorityDepthThree.Exact.Supplement
