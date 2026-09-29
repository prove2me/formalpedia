-- Prove2me | Theorems.Thm_FourExp_expPoly_ne_zero
-- name    : FourExp.expPoly_ne_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-14T19:31:19.481442+00:00
-- url     : https://prove2.me/theorems/62105f9b-bb74-4229-93da-4357e32498b8
-- title:
--   An exponential polynomial with distinct frequencies does not vanish identically
-- statement:
--   **An exponential polynomial with distinct frequencies is not identically zero.**
--
--   Let $\omega_1, \dots, \omega_l \in \mathbb{C}$ be pairwise distinct, let $q_1, \dots, q_l$ be non-negative integers, and let $b_{j,i}$ ($0 \le i < q_j$) be complex numbers, not all zero. Then the entire function
--   $$f(z) = \sum_{j=1}^{l} \sum_{i=0}^{q_j-1} b_{j,i}\, z^{i}\, e^{\omega_j z}$$
--   takes a non-zero value somewhere.
--
--   **Proof idea.** This is the classical linear independence of the functions $z^i e^{\omega_j z}$. Induct on $l$: multiply by $e^{-\omega_l z}$ and differentiate $q_l$ times. That kills the last block, and turns each other block into a polynomial of the same degree times $e^{(\omega_j - \omega_l)z}$, whose leading coefficient is multiplied by $(\omega_j - \omega_l)^{q_l} \ne 0$.
--
--   **What it is for.** `FourExp.expPoly_zero_count` counts zeros with `analyticOrderNatAt`, which is $0$ at every point of a function that vanishes identically. So a lower bound on the number of zeros only contradicts that count once $f \not\equiv 0$ is known. This node supplies that input to `FourExp.nonvanishing_derivative`, in the four exponentials subtree of the Diaz mission.
-- source:
--   Classical; see e.g. R. Tijdeman, Proc. Kon. Nederl. Akad. Wetensch. A 74 (1971), 1–7, or M. Waldschmidt, Bull. Soc. Math. France 99 (1971), 285–304, §4 (non-vanishing of the determinant (4.4)).

import Mathlib

namespace FourExp

theorem expPoly_ne_zero
    {l : ℕ} (q : Fin l → ℕ) (ω : Fin l → ℂ) (hω : Function.Injective ω)
    (b : (j : Fin l) → Fin (q j) → ℂ) (hb : ∃ j i, b j i ≠ 0) :
    ∃ w : ℂ, ∑ j, ∑ i : Fin (q j), b j i * w ^ (i : ℕ) * Complex.exp (ω j * w) ≠ 0 := by
  sorry

end FourExp
