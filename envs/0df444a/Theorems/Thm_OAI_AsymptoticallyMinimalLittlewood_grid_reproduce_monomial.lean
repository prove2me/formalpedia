-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_grid_reproduce_monomial
-- name    : OAI.AsymptoticallyMinimalLittlewood.grid_reproduce_monomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:51:26.791533+00:00
-- url     : https://prove2.me/theorems/71a7bf43-5c81-4e73-a6bc-4df3bdfb5d29
-- title:
--   The cross Dirichlet kernel $D_{2N}\overline{D_N}$ on an oversampled root grid reproduces the monomials $z^{k}$, $0\le k<N$
-- statement:
--   Let $M\ge 1$ be an integer and $\omega_j=e^{2\pi i j/M}$ for $j\in\mathbb{Z}/M\mathbb{Z}$. For an integer $n\ge 0$, a complex number $z$ and $j\in\mathbb{Z}/M\mathbb{Z}$, define the rotated Dirichlet kernel
--   $$
--   D_n(z;j)=\sum_{a=0}^{n-1}z^{a}\,\overline{\omega_j^{\,a}} .
--   $$
--   Let $N\ge 0$ with $2N\le M$, let $k$ be an integer with $0\le k<N$, and let $z\in\mathbb{C}$ with $|z|=1$. Then
--
--   $$
--   \sum_{j\in\mathbb{Z}/M\mathbb{Z}}\omega_j^{k}\,D_{2N}(z;j)\,\overline{D_N(z;j)}=M N\,z^{k} .
--   $$
--
--   By linearity, when $N\ge 1$ every polynomial $P(z)=\sum_{k=0}^{N-1}c_kz^{k}$ is therefore recovered on the unit circle from its values at the $M$-th roots of unity through
--   $$
--   P(z)=\frac{1}{MN}\sum_{j\in\mathbb{Z}/M\mathbb{Z}}P(\omega_j)\,D_{2N}(z;j)\,\overline{D_N(z;j)} .
--   $$
--   This interpolation formula with an oversampled grid ($M\ge 2N$) is the identity behind bounding a polynomial on the whole circle by its maximum on the grid.
--
--   **Formalization Note** The kernel $D_n(z;j)$ is `gridDirichlet n z j`, with $M$ implicit in the type `ZMod M` of $j$; $\omega_j$ is `ZMod.stdAddChar j`; the index $k$ is an element of `Fin N`; $M\ge 1$ is the instance `NeZero M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L1108-L1163

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

theorem OAI.AsymptoticallyMinimalLittlewood.grid_reproduce_monomial {M N : ℕ} [NeZero M] (hNM : 2 * N ≤ M)
    (k : Fin N) {z : ℂ} (hz : ‖z‖ = 1) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) * gridDirichlet (2 * N) z j *
      conj (gridDirichlet N z j)) = (M : ℂ) * N * z ^ (k : ℕ) := by sorry
