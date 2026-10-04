-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff89
-- name    : HlawkaSchatten.DiagonalCutoff.cutoff89
-- status  : Open
-- author  : @savarin
-- created : 2026-10-04T07:24:02.748985+00:00
-- url     : https://prove2.me/theorems/b2afdba8-fd6d-4c94-a924-101ef66e1ab7
-- title:
--   Sharp complex coordinate Hlawka constant for p ≥ 89
-- statement:
--   For a real exponent $p>1$ and a vector $x\in\mathbb C^n$, the
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
--   For every real $p\ge89$, the theorem asks for
--   $$
--   K_p=\min\{C\in\mathbb R:\ \forall n\in\mathbb N,\ \forall x,y,z\in\mathbb C^n,
--   \ \Delta_3\le C\Delta_2\}.
--   $$
--   This includes admissibility and uniform optimality, with all unequal-norm and
--   zero triples allowed. Dimension zero is included. No proof is known for
--   $89\le p<90$; the accepted cutoff-90 theorem covers every $p\ge90$.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.cutoff89 :
    ∀ p : ℝ, 89 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
