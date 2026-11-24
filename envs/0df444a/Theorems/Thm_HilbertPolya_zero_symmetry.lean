-- Prove2me | Theorems.Thm_HilbertPolya_zero_symmetry
-- name    : HilbertPolya.zero_symmetry
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T02:26:44.402044+00:00
-- url     : https://prove2.me/theorems/257aa1bc-dc6e-4b81-a221-b129b63f4502
-- title:
--   Riemann (1859): reflection symmetry of the nontrivial zeros
-- statement:
--   **Reflection symmetry of the zeros (Riemann, 1859).** For any complex number $s$ in the open critical strip $0<\Re(s)<1$,
--   $$\zeta(s)=0\quad\Longleftrightarrow\quad \zeta(1-s)=0.$$
--   Thus the nontrivial zeros are symmetric about the critical line $\Re(s)=\tfrac12$: reflection $s\mapsto 1-s$ permutes them. This is a consequence of Riemann's functional equation, which relates $\zeta(s)$ and $\zeta(1-s)$ through the completed zeta function $\Lambda(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)$ satisfying $\Lambda(s)=\Lambda(1-s)$.
--
--   In the spectral picture this symmetry corresponds to the eigenvalues being symmetric about $0$ (if $\gamma$ is an eigenvalue, so is $-\gamma$).
--
--   **Formalization Note.** The statement is restricted to the open strip, where both $s$ and $1-s$ avoid the pole at $1$ and the trivial zeros; it follows from Mathlib's `completedRiemannZeta_one_sub` together with the relation between `riemannZeta` and `completedRiemannZeta`.
-- source:
--   Riemann 1859, Über die Anzahl der Primzahlen unter einer gegebenen Grösse (functional equation); see Loeffler–Stoll 2025, https://arxiv.org/abs/2503.00959 , §3 (Mathlib `completedRiemannZeta_one_sub`, `riemannZeta_one_sub`).

import Mathlib

namespace HilbertPolya
theorem zero_symmetry :
    ∀ s : ℂ, 0 < s.re ∧ s.re < 1 → (riemannZeta s = 0 ↔ riemannZeta (1 - s) = 0) := by sorry
end HilbertPolya
