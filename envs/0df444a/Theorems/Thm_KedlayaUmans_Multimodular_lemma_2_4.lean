-- Prove2me | Theorems.Thm_KedlayaUmans_Multimodular_lemma_2_4
-- name    : KedlayaUmans.Multimodular.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:12.132157+00:00
-- url     : https://prove2.me/theorems/3d602c71-3ae2-4896-9cf0-d2e1c5771fb4
-- title:
--   Lemma 2.4 — the product of the primes $p \le 16\log N$ exceeds $N$
-- statement:
--   For every integer $N \ge 2$, the product of the primes less than or equal to $16\log N$ is greater than $N$:
--   $$\prod_{p \text{ prime},\; p \le 16\log N} p \;>\; N.$$
--
--   This is the number-theoretic input of the multimodular algorithm. It guarantees that the primes up to $16\log N$ are enough to recover, by the Chinese remainder theorem, any integer in $\{0,\dots,N\}$ from its residues.
--
--   **Formalization Note** $\log$ is the natural logarithm. The paper does not specify the base, and the natural log is the strongest reading, since $\ln N < \log_2 N$. "Primes $p \le x$" for real $x$ means primes $p \le \lfloor x \rfloor$.
-- source:
--   Kedlaya, Umans, Fast polynomial factorization and modular composition, Dagstuhl Seminar Proceedings 08381 (version of Aug. 31, 2008), p. 8, Lemma 2.4 (proof p. 9)

import Mathlib
import Definitions.Def_KedlayaUmans_Multimodular_Algorithm

namespace KedlayaUmans.Multimodular

/-- **Lemma 2.4.** For every integer `N ≥ 2`, the product of the primes `p ≤ 16 log N`
(natural logarithm) exceeds `N`. -/
theorem lemma_2_4 (N : ℕ) (hN : 2 ≤ N) :
    N < ∏ p ∈ primesUpTo (16 * Real.log (N : ℝ)), p := by sorry

end KedlayaUmans.Multimodular
