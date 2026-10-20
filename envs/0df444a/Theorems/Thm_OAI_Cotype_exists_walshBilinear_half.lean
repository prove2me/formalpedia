-- Prove2me | Theorems.Thm_OAI_Cotype_exists_walshBilinear_half
-- name    : OAI.Cotype.exists_walshBilinear_half
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:52:42.785371+00:00
-- url     : https://prove2.me/theorems/80137af5-071c-4df0-9c4f-1f59b13bcf37
-- title:
--   A bilinear test pair captures half the Walsh norm
-- statement:
--   Let $X,Y$ be real normed spaces, $n\in\mathbb N$ and $T:X\to Y$ a nonzero operator, with Walsh norm $\omega_n(T)$. Let
--   $$
--   \beta(f,g)=\mathbb E_u\,\mathbb E_v\,\chi_v(u)\,g(v)\bigl(Tf(u)\bigr)
--   $$
--   for $f:\{0,1\}^n\to X$ and $g:\{0,1\}^n\to Y^*$. There are $f,g$ with $\|f\|_{L_2}\le1$, $\|g\|_{L_2}\le1$ and $\beta(f,g)>\max(0,\omega_n(T)/2)$.
--
--   The Walsh norm is thus witnessed, up to a factor $2$, by a positive value of the bilinear form.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/WalshDuality.lean#L127-L143

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem OAI.Cotype.exists_walshBilinear_half (n : ℕ) {T : X →L[ℝ] Y} (hT : T ≠ 0) :
    ∃ f : Cube n → X, ∃ g : Cube n → (Y →L[ℝ] ℝ),
      cubeL2 X f ≤ 1 ∧ cubeL2 (Y →L[ℝ] ℝ) g ≤ 1 ∧
      walshNorm n T / 2 < walshBilinear T f g ∧ 0 < walshBilinear T f g := by sorry
