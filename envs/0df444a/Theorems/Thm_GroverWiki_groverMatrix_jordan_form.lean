-- Prove2me | Theorems.Thm_GroverWiki_groverMatrix_jordan_form
-- name    : GroverWiki.groverMatrix_jordan_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:41:27.777772+00:00
-- url     : https://prove2.me/theorems/af56a9a7-69f6-4490-b3d1-adceaec4aef9
-- title:
--   Jordan form of the Grover matrix: $U_sU_\omega = M\,\mathrm{diag}(e^{2it}, e^{-2it})\,M^{-1}$
-- statement:
--   Let $N \ge 2$, $t = \arcsin(1/\sqrt N)$, and let
--
--   $$A = \begin{bmatrix}1 & 2/\sqrt N\\ -2/\sqrt N & 1-4/N\end{bmatrix}, \qquad M = \begin{bmatrix}-i & i\\ e^{it} & e^{-it}\end{bmatrix}$$
--
--   be the matrix of $U_sU_\omega$ in the spanning set $\{|\omega\rangle, |s\rangle\}$ and the change-of-basis matrix. Then $M$ is invertible and
--
--   1. $A = M\begin{bmatrix}e^{2it} & 0\\ 0 & e^{-2it}\end{bmatrix}M^{-1}$;
--   2. for every $r \in \mathbb N$, $A^r = M\begin{bmatrix}e^{2rit} & 0\\ 0 & e^{-2rit}\end{bmatrix}M^{-1}$.
--
--   The diagonal form gives a closed formula for the state after any number of Grover iterations.
--
--   **Formalization Note** `M⁻¹` is Mathlib's matrix inverse, which is the zero matrix for a singular matrix; for $N \ge 2$ one has $t < \pi/2$, so $\det M = -2i\cos t \ne 0$. The hypothesis $N \ge 2$ excludes $N = 1$, where $M$ is singular.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, section "Algebraic proof" (PDF p. 6)

import Mathlib
import Definitions.Def_GroverWiki_Defs

open Matrix

namespace GroverWiki

/-- Algebraic proof: Jordan form of the matrix of `U_s U_ω` in the basis `{|ω⟩, |s⟩}`, and of its
`r`-th power. With `t = arcsin(1/√N)` and `M = [[-i, i], [e^{it}, e^{-it}]]`,
`U_s U_ω = M diag(e^{2it}, e^{-2it}) M⁻¹` and `(U_s U_ω)^r = M diag(e^{2rit}, e^{-2rit}) M⁻¹`. -/
theorem groverMatrix_jordan_form {N : ℕ} (hN : 2 ≤ N) :
    let t : ℝ := Real.arcsin (1 / Real.sqrt N)
    let A : Matrix (Fin 2) (Fin 2) ℂ :=
      !![1, 2 / (Real.sqrt N : ℂ); -2 / (Real.sqrt N : ℂ), 1 - 4 / (N : ℂ)]
    let M : Matrix (Fin 2) (Fin 2) ℂ :=
      !![-Complex.I, Complex.I; Complex.exp (t * Complex.I), Complex.exp (-(t * Complex.I))]
    A = M * !![Complex.exp (2 * t * Complex.I), 0; 0, Complex.exp (-(2 * t * Complex.I))] * M⁻¹ ∧
      ∀ r : ℕ, A ^ r =
        M * !![Complex.exp (2 * r * t * Complex.I), 0;
              0, Complex.exp (-(2 * r * t * Complex.I))] * M⁻¹ := by sorry

end GroverWiki
