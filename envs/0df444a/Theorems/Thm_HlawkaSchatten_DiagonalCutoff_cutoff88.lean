-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff88
-- name    : HlawkaSchatten.DiagonalCutoff.cutoff88
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T01:11:08.919986+00:00
-- url     : https://prove2.me/theorems/6630a599-f5c7-4d7f-a917-ee0230d52d55
-- title:
--   Sharp complex coordinate Hlawka constant for p ≥ 88
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
--   For every real $p\ge88$, the theorem asks for
--   $$
--   K_p=\min\{C\in\mathbb R:\ \forall n\in\mathbb N,\ \forall x,y,z\in\mathbb C^n,
--   \ \Delta_3\le C\Delta_2\}.
--   $$
--   This includes admissibility and uniform optimality, with all unequal-norm and
--   zero triples allowed. Dimension zero is included. This is the next step of the sharp diagonal Hlawka campaign below the cutoff-89 entry.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.cutoff88 :
    ∀ p : ℝ, 88 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
