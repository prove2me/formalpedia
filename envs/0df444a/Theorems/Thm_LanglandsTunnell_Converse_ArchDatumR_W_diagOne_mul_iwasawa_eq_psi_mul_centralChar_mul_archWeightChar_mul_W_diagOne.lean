-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
-- name    : LanglandsTunnell.Converse.ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/e3db6d9c-f426-59f2-8766-acd2ce947373
-- title:
--   Iwasawa factorisation of a weight-k archimedean Whittaker datum
-- statement:
--   Let $P$ be a real archimedean parameter and $D$ an `ArchDatumR P`, so that in particular its function $W : M_2(\mathbb{R}) \to \mathbb{C}$ satisfies the unipotent law $W(n(x)g) = \psi(x)W(g)$ with $\psi(x) = e^{2\pi i x}$ and the central law $W(z\cdot g) = \chi_P(z)\,|z|\,W(g)$ for $z \neq 0$, where $\chi_P$ is the central quasi-character `centralChar P` attached to $P$. Fix $k \in \mathbb{Z}$ and assume the weight law: for every $r$ in the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$ and every $x \in GL_2(\mathbb{R})$, $W(xr) = \chi_k(r)\,W(x)$, where $\chi_k(r)$ denotes `archWeightCharℝ k r` viewed in $\mathbb{C}$. Let $c \neq 0$, let $x \in \mathbb{R}$, let $y_1 \neq 0$, $y_2 > 0$, let $\theta \in \mathbb{R}$, and let $r$ be an element of `rowIsometrySubgroup₀ ℝ` whose underlying matrix is exactly the rotation $\begin{pmatrix}\cos\theta & -\sin\theta\\ \sin\theta & \cos\theta\end{pmatrix}$. Writing $d(t)$ for $\begin{pmatrix}t&0\\0&1\end{pmatrix}$, the conclusion is
--   $$W\!\left(d(c)\begin{pmatrix} y_1\cos\theta + xy_2\sin\theta & -y_1\sin\theta + xy_2\cos\theta \\ y_2\sin\theta & y_2\cos\theta\end{pmatrix}\right) = \psi(cx)\,\bigl(\chi_P(y_2)\,|y_2|\bigr)\,\bigl(\chi_k(r)\,W(d(cy_1/y_2))\bigr),$$
--   the displayed matrix being $n(x)\,\mathrm{diag}(y_1,y_2)\,\kappa_\theta$.
--
--   This is the factorisation of an archimedean Whittaker function in Iwasawa coordinates, reducing its value at $d(c)\,n(x)\,\mathrm{diag}(y_1,y_2)\,\kappa_\theta$ to the single variable $cy_1/y_2$, in the form adapted to a datum of $SO(2)$-weight $k$; the rotation is quantified as an arbitrary element of the row-isometry subgroup with its matrix pinned down, so that consumers may supply their own realisation of $\kappa_\theta$. It is used in the evaluation of the archimedean zeta and Rankin–Selberg integrals occurring in the converse-theorem input to Langlands–Tunnell.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open LanglandsTunnell.Converse.ArchR in

theorem LanglandsTunnell.Converse.ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_archWeightChar_mul_W_diagOne
    {P : RealArchParam} (D : ArchDatumR P) (k : ℤ)
    (hDW : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ)
    (r : rowIsometrySubgroup₀ ℝ)
    (hr : ((r : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![Real.cos θ, -Real.sin θ; Real.sin θ, Real.cos θ]) :
    D.W (ArchR.diagOne c * !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
         y₂ * Real.sin θ, y₂ * Real.cos θ]) =
      psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) *
        ((archWeightCharℝ k r : ℂ) * D.W (ArchR.diagOne (c * y₁ / y₂))) := by sorry
