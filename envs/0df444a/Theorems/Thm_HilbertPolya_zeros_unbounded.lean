-- Prove2me | Theorems.Thm_HilbertPolya_zeros_unbounded
-- name    : HilbertPolya.zeros_unbounded
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:27:12.986922+00:00
-- url     : https://prove2.me/theorems/f477e397-cbf3-45d3-88b9-75beb5deaf9c
-- title:
--   Riemann–von Mangoldt (1905), corollary: unbounded imaginary parts of the zeros
-- statement:
--   **Unboundedness of the zero ordinates (corollary of the Riemann–von Mangoldt formula, 1905).** For every real bound $M$ there is a nontrivial zero of the Riemann zeta function whose imaginary part exceeds $M$:
--   $$\forall M\in\mathbb R,\ \exists s\in\mathbb C:\ \zeta(s)=0,\ 0<\Re(s)<1,\ \Im(s)>M.$$
--   Thus the imaginary parts of the nontrivial zeros are unbounded above. This follows from the Riemann–von Mangoldt formula $N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+O(\log T)$, which tends to infinity with $T$ (and also from Hardy's theorem together with the fact that zeros are isolated).
--
--   This is the fact that forces any Hilbert–Pólya operator to be **unbounded**: a bounded operator has bounded spectrum, so it cannot have all the zero ordinates as eigenvalues.
--
--   **Formalization Note.** The statement is an unboundedness assertion (for every $M$ there exists a zero above it), not an asymptotic counting formula; the full Riemann–von Mangoldt formula is formalized in a sibling mission.
-- source:
--   Riemann 1859 (conjectured counting formula); von Mangoldt 1905 (proof); see Titchmarsh, The Theory of the Riemann Zeta-Function, 2nd ed., Oxford 1986, Theorem 9.4; https://en.wikipedia.org/wiki/Riemann%E2%80%93von_Mangoldt_formula

import Mathlib

namespace HilbertPolya
theorem zeros_unbounded :
    ∀ M : ℝ, ∃ s : ℂ, riemannZeta s = 0 ∧ 0 < s.re ∧ s.re < 1 ∧ M < s.im := by sorry
end HilbertPolya
