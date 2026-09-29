-- Prove2me | Theorems.Thm_ModularGroup_exists_finset_box_or_cusp
-- name    : ModularGroup.exists_finset_box_or_cusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/d9ad123a-b00a-5e78-a863-7fbbfe06358d
-- title:
--   Box-or-cusp cover for finite-index subgroups of SL₂(ℤ)
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ of finite index and let $Y$ be a real number. The assertion is that there exist a finite set $S$ of elements of $\mathrm{SL}_2(\mathbb{Z})$ and real numbers $B$, $y_0$, $Y_1$ with $y_0 > 0$, such that for every point $\tau$ of the upper half-plane $\mathbb{H}$ there is an element $\gamma \in \Gamma$ for which at least one of the following two alternatives holds for the point $\gamma \cdot \tau$ (the Möbius action of $\mathrm{SL}_2(\mathbb{Z})$ on $\mathbb{H}$): either $|\operatorname{Re}(\gamma\cdot\tau)| \le B$ and $y_0 \le \operatorname{Im}(\gamma\cdot\tau) \le Y_1$, so that $\gamma\cdot\tau$ lies in a fixed compact box depending only on $\Gamma$ and $Y$; or else $\gamma \cdot \tau = \sigma \cdot z$ for some $\sigma \in S$ and some $z$ in the standard fundamental domain `ModularGroup.fd` of $\mathrm{SL}_2(\mathbb{Z})$ with $\operatorname{Im} z > Y$. The data $S, B, y_0, Y_1$ are uniform in $\tau$; nothing is asserted about disjointness of the two alternatives, nor about any relation between $Y$ and $Y_1$.
--
--   This is the standard reduction-theoretic statement that every $\Gamma$-orbit in $\mathbb{H}$ meets either a fixed compact box or one of the finitely many cusp neighbourhoods $\sigma\{z \in \mathcal{D} : \operatorname{Im} z > Y\}$, $\sigma \in S$, for a finite-index subgroup $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$. It is used in the analytic estimates on modular curves, supplying the uniform dichotomy behind [`ModularCurve.JZero.exists_hyperplaneSection_defect_le`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_defect_le), [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge) and [`ModularCurve.JZero.exists_log_secVal_sub_le`](thm.html#ModularCurve.JZero.exists_log_secVal_sub_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularGroup_exists_finset_box_or_cusp.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped UpperHalfPlane MatrixGroups

theorem ModularGroup.exists_finset_box_or_cusp (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (Y : ℝ) :
    ∃ (S : Finset SL(2, ℤ)) (B y₀ Y₁ : ℝ), 0 < y₀ ∧ ∀ τ : ℍ, ∃ γ ∈ Γ,
      (|(γ • τ).re| ≤ B ∧ y₀ ≤ (γ • τ).im ∧ (γ • τ).im ≤ Y₁) ∨
      (∃ σ ∈ S, ∃ z ∈ ModularGroup.fd, Y < z.im ∧ γ • τ = σ • z) := by sorry
