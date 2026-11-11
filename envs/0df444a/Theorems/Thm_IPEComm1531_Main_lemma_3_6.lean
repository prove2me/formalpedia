-- Prove2me | Theorems.Thm_IPEComm1531_Main_lemma_3_6
-- name    : IPEComm1531.Main.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:39.842615+00:00
-- url     : https://prove2.me/theorems/e67965bf-7a71-4d07-a7b2-c13144796700
-- title:
--   Lemma 3.6 — Check accepts close pairs, only close pairs, and a nonzero difference is caught with probability $>2/5$
-- statement:
--   Let $(V_b)$ satisfy the conclusions of Theorem 3.2 and $x\mapsto p_x$ those of Lemma 3.3. For every tower length $r$ and all $x,z\in\{0,1\}^r$:
--
--   1. if $|x\oplus z|\le\delta r$, then $\mathrm{Check}(x,z,c)=1$ for some $c\in\{0,1\}^\ell$;
--   2. if $\mathrm{Check}(x,z,c)=1$ for some $c\in\{0,1\}^\ell$, then $|x\oplus z|\le8\delta r$;
--   3. for every $c\in\{0,1\}^\ell$ with $p_x a_c-p_z b_c\neq0$, for uniform $i\in[2r]$,
--   $$\Pr_i\big[p_x(i)a_c(i)=p_z(i)b_c(i)\big]<\frac35 .$$
--
--   These three properties drive both the protocol of Theorem 4.1 and the rectangle bound of Theorem 5.1.
--
--   Differences from the source:
--   - generalization: the spaces of Theorem 3.2 and the functions p_x of Lemma 3.3 → every family and assignment satisfying their correctness conclusions (no effectivity required); reason: the source proof uses only these conclusions; the source objects satisfy them
--   - encoding: probability over uniform i ∈ [2r] → number of agreeing positions divided by 2r; reason: uniform probability on a finite set
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Lemma 3.6, pp.9–10 (proof in Appendix C, pp.18–19)

import Mathlib
import Definitions.Def_IPEComm1531_Main_Construction

namespace IPEComm1531.Main

open Classical in
/-- Lemma 3.6 (properties of Check), pp.9–10. -/
theorem lemma_3_6 (S : Spaces) (p : Prescribed) (hS : S.Good) (hp : PrescribedCorrect S p)
    (j : ℕ) (x z : Bits (radius j)) :
    (distance x z ≤ slack j → ∃ c : Bits (certificateLength S j), Check S p j x z c) ∧
    ((∃ c : Bits (certificateLength S j), Check S p j x z c) → distance x z ≤ 8 * slack j) ∧
    (∀ c : Bits (certificateLength S j), p j x * certA S j c - p j z * certB S j c ≠ 0 →
      ((Finset.univ.filter fun i : Fin (2 * radius j) =>
          p j x i * certA S j c i = p j z i * certB S j c i).card : ℝ) /
        (2 * radius j : ℝ) < 3 / 5) := by sorry

end IPEComm1531.Main
