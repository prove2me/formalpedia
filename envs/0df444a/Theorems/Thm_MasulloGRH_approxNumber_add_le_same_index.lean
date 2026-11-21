-- Prove2me | Theorems.Thm_MasulloGRH_approxNumber_add_le_same_index
-- name    : MasulloGRH.approxNumber_add_le_same_index
-- status  : Disproved
-- author  : @marozols
-- created : 2026-11-21T01:04:13.074419+00:00
-- url     : https://prove2.me/theorems/ac4831ba-e3dc-4ba2-afeb-0049ab739c30
-- title:
--   Lemma C.3.6.3(1) as printed — $\sigma_m(A+B)\le\sigma_m(A)+\sigma_m(B)$
-- statement:
--   This node records part (1) of Lemma C.3.6.3 of the draft **exactly as printed**, so that it can be checked.
--
--   For Hilbert spaces $E,F$ and a bounded operator $T\colon E\to F$, the draft defines (equation (C.3.6.2)) the $k$-th approximation number
--   $$\sigma_k(T)=\inf\bigl\{\|A-T\| : A\in\mathscr L(E,F),\ \dim\operatorname{Im}(A)\le k-1\bigr\},\qquad k\ge1,$$
--   which for compact $T$ on a single Hilbert space is the $k$-th singular value. Lemma C.3.6.3(1) then states, for every integer $m\ge1$ and all $A,B\in\mathscr L(E,F)$:
--   $$\sigma_m(A+B)\le\sigma_m(A)+\sigma_m(B).$$
--
--   Note that the same index $m$ appears on both sides. (The classical inequality for approximation numbers is $\sigma_{m+n-1}(A+B)\le\sigma_m(A)+\sigma_n(B)$; see Jarchow, *Locally Convex Spaces*, §19.8, Prop. 1, which the draft cites.)
--
--   **Formalization Note** No separate definition is introduced: $\sigma_k(T)$ is written out as the infimum of the set of reals $\|T-R\|$ over bounded operators $R$ whose range is finite-dimensional of dimension $<k$ (that is, $\le k-1$). The spaces are taken in the lowest universe, which is enough to test the statement.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Appendix C, Lemma C.3.6.3 part (1) and equation (C.3.6.2), p. 704

import Mathlib

set_option autoImplicit false

namespace MasulloGRH

theorem approxNumber_add_le_same_index (E F : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (m : ℕ) (hm : 1 ≤ m) (A B : E →L[ℂ] F) :
    sInf {r : ℝ | ∃ R : E →L[ℂ] F,
        FiniteDimensional ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) ∧
        Module.finrank ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) < m ∧ r = ‖(A + B) - R‖} ≤
      sInf {r : ℝ | ∃ R : E →L[ℂ] F,
        FiniteDimensional ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) ∧
        Module.finrank ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) < m ∧ r = ‖A - R‖} +
      sInf {r : ℝ | ∃ R : E →L[ℂ] F,
        FiniteDimensional ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) ∧
        Module.finrank ℂ (LinearMap.range (R : E →ₗ[ℂ] F)) < m ∧ r = ‖B - R‖} := by sorry

end MasulloGRH
