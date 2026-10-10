-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound70
-- name    : HlawkaSchatten.DiagonalCutoff.real_bound70
-- status  : Proved
-- author  : @savarin
-- created : 2026-10-08T04:00:50.969977+00:00
-- url     : https://prove2.me/theorems/e7507661-98b6-4e15-a687-34cdb0525997
-- title:
--   The real coordinate Hlawka bound for p ≥ 70
-- statement:
--   For a real exponent $p>1$ and a vector $x\in\mathbb R^n$, the
--   **coordinate norm** is
--   $$
--   N_p(x)=\left(\sum_{i=1}^n|x_i|^p\right)^{1/p}.
--   $$
--   For any three vectors in the same space, their **triple deficit** is
--   $$
--   \Delta_3=N_p(x)+N_p(y)+N_p(z)-N_p(x+y+z),
--   $$
--   and their **pair-deficit sum** is
--   $$
--   \Delta_2=2\bigl(N_p(x)+N_p(y)+N_p(z)\bigr)
--   -N_p(x+y)-N_p(x+z)-N_p(y+z).
--   $$
--   A real constant $C$ is uniformly admissible when
--   $\Delta_3\le C\Delta_2$ for every triple and every finite dimension.
--
--   For $t\in[1/2,2]$, define
--   $$
--   A_p(t)=(t^p+2)^{1/p},\qquad
--   B_p(t)=(2|1-t|^p+2^p)^{1/p},
--   $$
--   $$
--   R_p(t)=\frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)},
--   \qquad K_p=\sup_{t\in[1/2,2]}R_p(t).
--   $$
--   This **cyclic constant** is exactly the foundation's `cyclicConstant`.
--   It comes from the three vectors $(-t,1,1),(1,-t,1),(1,1,-t)$.
--   The fixed compact interval and the absolute value in $B_p$ are part of
--   the definition and remain unchanged in this task.
--   [Cyclic definitions](https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Cyclic.lean)
--
--   The theorem asks for
--   $$
--   \forall p\ge70,\ \forall n\in\mathbb N,\ \forall x,y,z\in\mathbb R^n,
--   \qquad \Delta_3\le K_p\Delta_2.
--   $$
--   There is no equal-norm, normalization or nonzero restriction. The finite
--   dimension may be zero. This is the real admissibility statement, without a
--   leastness assertion. The accepted real bound covers every $p\ge80$.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.real_bound70 :
    ∀ p : ℝ, 70 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by sorry
