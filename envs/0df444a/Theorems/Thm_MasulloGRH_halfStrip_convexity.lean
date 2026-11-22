-- Prove2me | Theorems.Thm_MasulloGRH_halfStrip_convexity
-- name    : MasulloGRH.halfStrip_convexity
-- status  : Proved
-- author  : @flashonfire
-- created : 2026-11-21T19:13:28.1358+00:00
-- url     : https://prove2.me/theorems/8dd9b038-f669-40a5-a6c9-bc85679506f4
-- title:
--   Phragmén–Lindelöf convexity on half-strips with interpolated exponent
-- statement:
--   **Phragmén–Lindelöf convexity on half-strips.** Let $a<b$, $T\ge1$, and let $f$ be holomorphic on a neighbourhood of each point of the two closed half-strips
--   $$\Sigma_T=\{s\in\mathbb C:\ a\le\operatorname{Re}s\le b,\ |\operatorname{Im}s|\ge T\}.$$
--   Suppose $f$ has polynomial growth there, $|f(s)|\le A|\operatorname{Im}s|^M$ on $\Sigma_T$, and satisfies the edge bounds
--   $$|f(a+it)|\le A|t|^{\alpha},\qquad |f(b+it)|\le A|t|^{\beta}\qquad(|t|\ge T).$$
--   Then there are constants $C$ and $T'$ such that, for all $s=\sigma+it\in\Sigma_{T'}$,
--   $$|f(\sigma+it)|\le C\,|t|^{\ell(\sigma)},\qquad \ell(\sigma)=\alpha\frac{b-\sigma}{b-a}+\beta\frac{\sigma-a}{b-a},$$
--   that is, with the exponent interpolated linearly between the two edges (no loss of $\varepsilon$).
--
--   This is the classical Phragmén–Lindelöf convexity principle in the $t$-aspect (see e.g. Titchmarsh, *The Theory of Functions*, or Iwaniec–Kowalski, *Analytic Number Theory*, §5). It is stated on half-strips rather than full strips so that it applies to $L$-functions that may have poles at bounded height. The usual proof multiplies $f$ by an auxiliary holomorphic function of modulus $\asymp|t|^{-\ell(\sigma)}$ on each half-strip and applies the bounded form of Phragmén–Lindelöf (Mathlib's `PhragmenLindelof.vertical_strip`-type statements), using that $f$ is bounded on the compact bottom segments by continuity.
-- source:
--   A. M. Masullo, The Music of the Primes (draft of 20 November 2026), Appendix B, Proposition B.1.1.3 (Convexity Bound), p. 591. Reconstruction: supporting lemma for the standard Phragmén–Lindelöf proof of B.1.1.3.

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

theorem halfStrip_convexity (f : ℂ → ℂ) (a b α β M A T : ℝ) (hab : a < b) (hT : 1 ≤ T)
    (hd : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → DifferentiableAt ℂ f s)
    (hgrowth : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T ≤ |s.im| → ‖f s‖ ≤ A * |s.im| ^ M)
    (ha : ∀ t : ℝ, T ≤ |t| → ‖f ((a : ℂ) + t * Complex.I)‖ ≤ A * |t| ^ α)
    (hb : ∀ t : ℝ, T ≤ |t| → ‖f ((b : ℂ) + t * Complex.I)‖ ≤ A * |t| ^ β) :
    ∃ C T' : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → T' ≤ |s.im| →
      ‖f s‖ ≤ C * |s.im| ^ (α * (b - s.re) / (b - a) + β * (s.re - a) / (b - a)) := by
  sorry

end MasulloGRH
