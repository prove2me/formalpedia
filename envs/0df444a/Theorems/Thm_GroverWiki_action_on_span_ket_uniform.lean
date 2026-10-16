-- Prove2me | Theorems.Thm_GroverWiki_action_on_span_ket_uniform
-- name    : GroverWiki.action_on_span_ket_uniform
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:40:31.578992+00:00
-- url     : https://prove2.me/theorems/7485c39c-df80-4d0b-ad4e-b8c3a5783803
-- title:
--   Action of $U_s$ and $U_\omega$ on $\mathrm{span}\{|\omega\rangle, |s\rangle\}$
-- statement:
--   Let $f\colon\{0,\dots,N-1\}\to\{0,1\}$ have exactly one index $\omega$ with $f(\omega) = 1$. For all $a, b \in \mathbb C$,
--
--   $$U_s\bigl(a|\omega\rangle + b|s\rangle\bigr) = -a\,|\omega\rangle + \Bigl(\frac{2a}{\sqrt N} + b\Bigr)|s\rangle, \qquad U_\omega\bigl(a|\omega\rangle + b|s\rangle\bigr) = \Bigl(-a - \frac{2b}{\sqrt N}\Bigr)|\omega\rangle + b\,|s\rangle .$$
--
--   In the spanning set $\{|\omega\rangle, |s\rangle\}$ the two operators are thus given by the matrices $\begin{bmatrix}-1 & 0\\ 2/\sqrt N & 1\end{bmatrix}$ and $\begin{bmatrix}-1 & -2/\sqrt N\\ 0 & 1\end{bmatrix}$, and their product $U_sU_\omega$ by $\begin{bmatrix}1 & 2/\sqrt N\\ -2/\sqrt N & 1-4/N\end{bmatrix}$; this reduces the analysis of the algorithm to a $2\times2$ matrix.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Algebraic proof" (PDF pp. 5–6)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Algebraic proof: action of `U_s` and `U_ω` in the span of `{|ω⟩, |s⟩}`:
`U_s : a|ω⟩ + b|s⟩ ↦ -a|ω⟩ + (2a/√N + b)|s⟩` and
`U_ω : a|ω⟩ + b|s⟩ ↦ (-a - 2b/√N)|ω⟩ + b|s⟩`. -/
theorem action_on_span_ket_uniform {N : ℕ} (f : Fin N → Fin 2) (ω : Fin N)
    (hω : ∀ x, f x = 1 ↔ x = ω) (a b : ℂ) :
    diffusion N *ᵥ (a • ket ω + b • uniformState N) =
        (-a) • ket ω + (2 * a / (Real.sqrt N : ℂ) + b) • uniformState N ∧
      phaseOracle f *ᵥ (a • ket ω + b • uniformState N) =
        (-a - 2 * b / (Real.sqrt N : ℂ)) • ket ω + b • uniformState N := by sorry

end GroverWiki
