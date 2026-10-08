-- Prove2me | Theorems.Thm_FrieszDUE_FIFO_lemma_1
-- name    : FrieszDUE.FIFO.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:07:44.921451+00:00
-- url     : https://prove2.me/theorems/1e4a1493-2a6a-4e0b-b0bd-b90fe3994ca1
-- title:
--   Lemma 1, p. 185 — derivative of the inverse: [f⁻¹]′(z) = 1/f′[f⁻¹(z)]
-- statement:
--   Let $f : \mathbb R \to \mathbb R$ be differentiable and invertible, with inverse $f^{-1}$, so that $f^{-1}[f(t)] = t$ and $f[f^{-1}(z)] = z$ for all $t, z$. If $z \in \mathbb R$ is a point with $f'[f^{-1}(z)] \ne 0$, then $f^{-1}$ is differentiable at $z$ and
--   $$[f^{-1}]'(z) = \frac{1}{f'[f^{-1}(z)]} .$$
--
--   This is the inverse-function rule used in the proof of Theorem 1 to differentiate the lower limit $\tau_1^{-1}(t)$ of the volume integral (26).
--
--   **Formalization Note** The hypothesis $f'[f^{-1}(z)] \ne 0$ is added: the page omits it, and without it the statement fails ($f(t) = t^3$ at $z = 0$). In the paper's application the derivative is $\ge 1 + \alpha u > 0$, so the addition costs nothing there.
-- source:
--   Friesz, Bernstein, Smith, Tobin and Wie, A variational inequality formulation of the dynamic network user equilibrium problem, Oper. Res. 41 (1993), p. 185, Lemma 1, (19)

import Mathlib

namespace FrieszDUE.FIFO

theorem lemma_1 (f g : ℝ → ℝ) (hgf : Function.LeftInverse g f)
    (hfg : Function.RightInverse g f) (hf : Differentiable ℝ f) (z : ℝ)
    (hz : deriv f (g z) ≠ 0) :
    HasDerivAt g (1 / deriv f (g z)) z := by sorry

end FrieszDUE.FIFO
