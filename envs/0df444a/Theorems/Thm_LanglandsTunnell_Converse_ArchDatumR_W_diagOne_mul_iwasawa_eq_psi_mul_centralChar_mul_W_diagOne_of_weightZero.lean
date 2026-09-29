-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero
-- name    : LanglandsTunnell.Converse.ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/e57449f4-961a-501a-b62d-be2b98ba69a9
-- title:
--   Weight-zero Whittaker datum on the Iwasawa matrix
-- statement:
--   Let $P$ be a real archimedean parameter and let $D$ be an archimedean Whittaker datum `ArchDatumR P`; of its data only the function $W \colon M_2(\mathbb{R}) \to \mathbb{C}$, the unipotent law $W(\mathrm{unip}(t)\,g) = \psi(t)\,W(g)$ with $\psi(t) = e^{2\pi i t}$, and the central law $W(z \cdot g) = \chi_P(z)\,|z|\,W(g)$ for $z \neq 0$ (where $\chi_P$ is the quasicharacter `centralChar P` built from the central exponent and central sign of $P$) enter the statement. Assume further that $W$ is right-invariant under the subgroup `rowIsometrySubgroup₀ ℝ` of $GL_2(\mathbb{R})$ — determinant-one matrices whose rows act isometrically for the Euclidean norm, i.e. $SO(2)$ — in the sense that $W(x r) = W(x)$ for every $r$ in that subgroup and every $x \in GL_2(\mathbb{R})$ (weight zero). Let $c \neq 0$, let $x, \theta \in \mathbb{R}$, let $y_1 \neq 0$ and $y_2 > 0$. Writing $\mathrm{diagOne}(t) = \begin{pmatrix} t & 0 \\ 0 & 1\end{pmatrix}$, the conclusion is the identity $$W\left(\mathrm{diagOne}(c) \begin{pmatrix} y_1\cos\theta + x y_2 \sin\theta & -y_1 \sin\theta + x y_2 \cos\theta \\ y_2 \sin\theta & y_2\cos\theta\end{pmatrix}\right) = \psi(cx)\,\bigl(\chi_P(y_2)\,|y_2|\bigr)\,W\bigl(\mathrm{diagOne}(c y_1/y_2)\bigr),$$ the second matrix being the Iwasawa product $n(x)\,\mathrm{diag}(y_1,y_2)\,\kappa_\theta$ written out entrywise.
--
--   This is the factorisation of an archimedean Whittaker function of $SO(2)$-weight zero along Iwasawa coordinates, reducing all values on $\mathrm{diag}(c,1)\,n(x)\,\mathrm{diag}(y_1,y_2)\,\kappa_\theta$ to the one-variable function $t \mapsto W(\mathrm{diagOne}(t))$ together with the additive character and the central quasicharacter. It is the common input to the three weight-zero integral computations [`LanglandsTunnell.Converse.integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero`](thm.html#LanglandsTunnell.Converse.integral_dualConfig_blockHarmonic_eq_two_pi_mul_integral_iwasawa_of_weightZero), [`LanglandsTunnell.Converse.integral_dualConfig_detPow_blockQuadratic_colHarmonicTwo_eq_two_pi_mul_integral_iwasawa_of_weightZero`](thm.html#LanglandsTunnell.Converse.integral_dualConfig_detPow_blockQuadratic_colHarmonicTwo_eq_two_pi_mul_integral_iwasawa_of_weightZero) and [`LanglandsTunnell.Converse.integral_dualConfig_minor_eq_two_pi_mul_integral_iwasawa_of_weightZero`](thm.html#LanglandsTunnell.Converse.integral_dualConfig_minor_eq_two_pi_mul_integral_iwasawa_of_weightZero) in the converse-theorem part of the Langlands–Tunnell argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_ArchDatumR_W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetVector3
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.Converse MeasureTheory

open LanglandsTunnell.Converse.ArchR in

theorem LanglandsTunnell.Converse.ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero
    {P : RealArchParam} (D : ArchDatumR P)
    (hDW0 : ∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (ArchR.diagOne c * !![y₁ * Real.cos θ + x * y₂ * Real.sin θ, -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
         y₂ * Real.sin θ, y₂ * Real.cos θ]) =
      psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ)) * D.W (ArchR.diagOne (c * y₁ / y₂)) := by sorry
