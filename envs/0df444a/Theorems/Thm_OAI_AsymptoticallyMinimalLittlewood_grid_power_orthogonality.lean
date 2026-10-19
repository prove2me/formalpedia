-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_grid_power_orthogonality
-- name    : OAI.AsymptoticallyMinimalLittlewood.grid_power_orthogonality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:49:42.604347+00:00
-- url     : https://prove2.me/theorems/7277ee97-fc1c-4d21-87ec-b4a3239a08a1
-- title:
--   Orthogonality of the monomials $z^{0},\dots,z^{M-1}$ on the $M$-th roots of unity
-- statement:
--   Let $M\ge 1$ be an integer and, for $j\in\mathbb{Z}/M\mathbb{Z}$, let $\omega_j=e^{2\pi i j/M}$ be the corresponding $M$-th root of unity. For all integers $a,b$ with $0\le a,b<M$,
--
--   $$
--   \sum_{j\in\mathbb{Z}/M\mathbb{Z}}\omega_j^{a}\,\overline{\omega_j^{\,b}}=\begin{cases}M, & a=b,\\ 0, & a\ne b.\end{cases}
--   $$
--
--   Equivalently, the monomials $z^{0},z^{1},\dots,z^{M-1}$ are orthogonal for the counting measure on the $M$-th roots of unity, each having squared norm $M$; these are the characters of the cyclic group $\mathbb{Z}/M\mathbb{Z}$. This relation is the basic tool for evaluating discrete sums of products of polynomials over a root-of-unity grid.
--
--   **Formalization Note** The root $\omega_j$ is Mathlib's standard additive character `ZMod.stdAddChar j` of `ZMod M`, equal to $\exp(2\pi i\,\mathrm{val}(j)/M)$; the hypothesis $M\ge 1$ is the instance `NeZero M`, and $a,b$ are natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Rounding.lean#L1038-L1056

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

theorem OAI.AsymptoticallyMinimalLittlewood.grid_power_orthogonality {M a b : ℕ} [NeZero M] (ha : a < M) (hb : b < M) :
    (∑ j : ZMod M, ZMod.stdAddChar j ^ a * conj (ZMod.stdAddChar j ^ b)) =
      if a = b then (M : ℂ) else 0 := by sorry
