-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_grid_dirichlet_square
-- name    : OAI.AsymptoticallyMinimalLittlewood.grid_dirichlet_square
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:50:50.264116+00:00
-- url     : https://prove2.me/theorems/b3914753-72fb-4136-8fb1-c720cfe064f6
-- title:
--   Mean square of a rotated Dirichlet kernel over the $M$-th roots of unity equals $n$
-- statement:
--   Let $M\ge 1$ be an integer and $\omega_j=e^{2\pi i j/M}$ for $j\in\mathbb{Z}/M\mathbb{Z}$. Let $0\le n\le M$ and let $z\in\mathbb{C}$ with $|z|=1$. Then
--
--   $$
--   \sum_{j\in\mathbb{Z}/M\mathbb{Z}}\Bigl|\sum_{a=0}^{n-1}z^{a}\,\overline{\omega_j^{\,a}}\Bigr|^{2}=M\,n .
--   $$
--
--   The inner sum is the Dirichlet kernel $D_n(w)=\sum_{a=0}^{n-1}w^{a}$ evaluated at the rotated grid point $w=z\,\overline{\omega_j}$. The identity says that the average of $|D_n|^{2}$ over the $M$ points $z\overline{\omega_j}$ is exactly $n$, the same as its average over the whole circle, for every rotation $z$, provided the grid has at least $n$ points. Combined with the Cauchy–Schwarz inequality, it bounds sums of products of two such kernels.
--
--   **Formalization Note** The root $\omega_j$ is `ZMod.stdAddChar j`, the hypothesis $M\ge 1$ is the instance `NeZero M`, and the summation index $a$ ranges over `Fin n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L1058-L1102

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding

open OAI OAI.AsymptoticallyMinimalLittlewood
universe u v w
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff
open scoped ComplexConjugate
open Finset

theorem OAI.AsymptoticallyMinimalLittlewood.grid_dirichlet_square {M n : ℕ} [NeZero M] (hn : n ≤ M)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ‖∑ a : Fin n, z ^ (a : ℕ) * conj (ZMod.stdAddChar j ^ (a : ℕ))‖ ^ 2) =
      (M : ℝ) * n := by sorry
