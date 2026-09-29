-- Prove2me | Theorems.Thm_ModularCurve_coeff_tateToricPoint_mem_of_mem
-- name    : ModularCurve.coeff_tateToricPoint_mem_of_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/2deed33c-5e64-5127-b1ec-07dc2e268ca4
-- title:
--   Integrality of the toric Tate point's q-coefficients
-- statement:
--   Let $R$ be a commutative ring, $p$ a natural number, $B \subseteq R$ a subring and $c \in R^{\times}$ a unit with both $c$ and $c^{-1}$ lying in $B$. The pair [`ModularCurve.tateToricPoint R p c`](def/ModularCurve_KatzLevelPCusps.html#L20) consists of two Laurent series over $R$ (Hahn series over $\mathbb{Z}$), each obtained from a power series by `HahnSeries.ofPowerSeries`: the first has $m$-th coefficient $c\,\mathrm{inverse}(1-c)^2$ for $m = 0$ and, for $m > 0$, $\sum_{d \mid m,\ p \mid d} (m/d)\bigl(c^{m/d} + (c^{-1})^{m/d}\bigr) - 2\bigl[p \mid m\bigr]\sum_{e \mid m/p} e$; the second has $m$-th coefficient $c^{2}\,\mathrm{inverse}(1-c)^{3}$ for $m = 0$ and, for $m > 0$, $\sum_{d \mid m,\ p \mid d}\bigl(\binom{m/d}{2}c^{m/d} - \binom{m/d+1}{2}(c^{-1})^{m/d}\bigr) + \bigl[p \mid m\bigr]\sum_{e \mid m/p} e$, where $\mathrm{inverse}$ is `Ring.inverse`. The assertion is fourfold: for every $m > 0$ the coefficients of both components at $m$ lie in $B$; the constant coefficient of the first component equals $c\,\mathrm{inverse}(1-c)^{2}$ and that of the second equals $c^{2}\,\mathrm{inverse}(1-c)^{3}$; and for every integer $k < 0$ both components have vanishing coefficient at $k$.
--
--   This records that the $x$- and $y$-coordinates of the toric point $u = c$ on the Tate curve with parameter $\mathsf q^{p}$ have all strictly positive $q$-coefficients in any subring containing $c$ and $c^{-1}$ (so, integrally, in $\mathbb{Z}[c, c^{-1}]$), while the only non-integral contributions are the constant terms $c(1-c)^{-2}$ and $c^{2}(1-c)^{-3}$, and no negative powers of $q$ occur. It is used in the analysis of the behaviour of Drinfeld-basis points at the cusps, feeding the statements that a toric Tate point lies in the non-units of the relevant local ring and that the corresponding point of the modular curve reduces to the origin on the chart at the cusp.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_tateToricPoint_mem_of_mem.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.coeff_tateToricPoint_mem_of_mem
    (R : Type*) [CommRing R] (p : ℕ) (B : Subring R) (c : Rˣ) (hc : (c : R) ∈ B) (hc' : ((c⁻¹ : Rˣ) : R) ∈ B) :
    (∀ m : ℕ, 0 < m → ((ModularCurve.tateToricPoint R p c).1.coeff (m : ℤ) ∈ B ∧
      (ModularCurve.tateToricPoint R p c).2.coeff (m : ℤ) ∈ B)) ∧
    (ModularCurve.tateToricPoint R p c).1.coeff 0 = (c : R) * Ring.inverse (1 - (c : R)) ^ 2 ∧
    (ModularCurve.tateToricPoint R p c).2.coeff 0 = (c : R) ^ 2 * Ring.inverse (1 - (c : R)) ^ 3 ∧
    (∀ k : ℤ, k < 0 → (ModularCurve.tateToricPoint R p c).1.coeff k = 0 ∧ (ModularCurve.tateToricPoint R p c).2.coeff k = 0) := by sorry
