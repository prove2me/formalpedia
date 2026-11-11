-- Prove2me | Theorems.Thm_IPEComm1531_Main_theorem_5_1
-- name    : IPEComm1531.Main.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:42.467798+00:00
-- url     : https://prove2.me/theorems/7f937b2a-156b-4035-9477-15db0e018d5f
-- title:
--   Theorem 5.1 — every monochromatic rectangle of $\mathrm{IPE}_n$ has density $2^{-\Omega(n)}$
-- statement:
--   Let the spaces, extractor and prescribed-zero functions satisfy the correctness conclusions of Theorem 3.2, Fact 2.3 and Lemma 3.3 (with no algorithmic effectivity assumed), and let $\mathrm{IPE}_n$ be the resulting function on $n$-bit input pairs. There are $c>0$ and $N$ such that for every $n\ge N$ and all $A,B\subseteq\{0,1\}^n$ on which $\mathrm{IPE}_n$ is constant (of either value),
--   $$\frac{|A||B|}{2^{2n}}\le2^{-cn}.$$
--
--   This is the rectangle half of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: the specific objects constructed in Fact 2.3, Theorem 3.2 and Lemma 3.3 → every family satisfying the correctness conclusions of Fact 2.3, Theorem 3.2 and Lemma 3.3, with no algorithmic effectivity required; reason: the communication and rectangle arguments use only correctness, since local computation is uncharged; the source objects satisfy these hypotheses, so the Lean statement specializes to the source
--   - encoding: every monochromatic rectangle has density at most 2^{−Ω(n)} under the uniform distribution → ∃ c > 0, N such that for n ≥ N every monochromatic A × B of n-bit inputs has |A||B|/2^{2n} ≤ 2^{−cn}; reason: unpacking of Ω(·); density on the full n-bit inputs, as in the last paragraph of the proof
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Theorem 5.1, p.11 (proof pp.11–13)

import Mathlib
import Definitions.Def_IPEComm1531_Main_Construction

namespace IPEComm1531.Main

/-- Theorem 5.1 (all monochromatic rectangles of IPE are small), p.11. -/
theorem theorem_5_1 (S : Spaces) (E : Extractors) (p : Prescribed)
    (hS : S.Good) (hE : E.Good) (hp : PrescribedCorrect S p) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ A B : Finset (Fin n → Bool), Monochromatic (family S E p n) A B →
        rectangleDensity A B ≤ (2 : ℝ) ^ (-(c * n)) := by sorry

end IPEComm1531.Main
