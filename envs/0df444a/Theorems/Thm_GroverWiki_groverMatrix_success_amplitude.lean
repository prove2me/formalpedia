-- Prove2me | Theorems.Thm_GroverWiki_groverMatrix_success_amplitude
-- name    : GroverWiki.groverMatrix_success_amplitude
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T14:41:48.638728+00:00
-- url     : https://prove2.me/theorems/cffc4011-a5f4-4ad4-82ca-3a48aa1d73ee
-- title:
--   Algebraic proof: probability of observing $\omega$ after $r$ iterations is $\sin^2((2r+1)t)$
-- statement:
--   Let $N \ge 1$, $t = \arcsin(1/\sqrt N)$, and let $A = \begin{bmatrix}1 & 2/\sqrt N\\ -2/\sqrt N & 1-4/N\end{bmatrix}$ be the matrix of $U_sU_\omega$ in the spanning set $\{|\omega\rangle, |s\rangle\}$. Since $\langle\omega|\omega\rangle = 1$ and $\langle\omega|s\rangle = 1/\sqrt N$, for every $r \in \mathbb N$
--
--   $$\left|\begin{bmatrix}\langle\omega|\omega\rangle & \langle\omega|s\rangle\end{bmatrix} A^r \begin{bmatrix}0\\ 1\end{bmatrix}\right|^2 = \left|\begin{bmatrix}1 & \tfrac{1}{\sqrt N}\end{bmatrix} A^r \begin{bmatrix}0\\ 1\end{bmatrix}\right|^2 = \sin^2\bigl((2r+1)t\bigr).$$
--
--   The left-hand side is the probability of observing $\omega$ after $r$ iterations, computed in coordinates; this recovers the formula of the geometric proof, since $(2r+1)t = (r+\frac12)\theta$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Algebraic proof" (PDF p. 6)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Algebraic proof: the probability of observing `ω` after `r` iterations, computed from the
`2 × 2` matrix of `U_s U_ω` in the basis `{|ω⟩, |s⟩}`:
`|[⟨ω|ω⟩ ⟨ω|s⟩] (U_s U_ω)^r [0, 1]ᵀ|² = sin²((2r+1)t)` with `t = arcsin(1/√N)`. -/
theorem groverMatrix_success_amplitude {N : ℕ} (hN : 1 ≤ N) (r : ℕ) :
    ‖![(1 : ℂ), 1 / (Real.sqrt N : ℂ)] ⬝ᵥ
        ((!![1, 2 / (Real.sqrt N : ℂ); -2 / (Real.sqrt N : ℂ), 1 - 4 / (N : ℂ)] ^ r) *ᵥ
          ![0, 1])‖ ^ 2 =
      Real.sin ((2 * r + 1) * Real.arcsin (1 / Real.sqrt N)) ^ 2 := by sorry

end GroverWiki
